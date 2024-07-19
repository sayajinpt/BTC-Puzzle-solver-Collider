#include <iostream>
#include <limits>
#include <fstream>
#include <sstream>
#include <iomanip>
#include <random>
#include <vector>
#include <unordered_set>
#include <tuple>
#include <thread>
#include <atomic>
#include <mutex>
#include <chrono>
#include <boost/multiprecision/cpp_int.hpp>
#include <openssl/sha.h>
#include <openssl/ripemd.h>

using namespace std;
namespace mp = boost::multiprecision;

// Elliptic curve parameters (secp256k1)
const mp::cpp_int P("115792089237316195423570985008687907853269984665640564039457584007908834671663");
const mp::cpp_int A = 0;
const mp::cpp_int B = 7;
const mp::cpp_int Gx("55066263022277343669578718895168534326250603453777594175500187360389116729240");
const mp::cpp_int Gy("32670510020758816978083085130507043184471273380659243275938904335757337482424");

using Point = std::tuple<mp::cpp_int, mp::cpp_int, mp::cpp_int>;


// Global shared counter and mutex
std::atomic<long long> globalCounter(0);
std::mutex counterMutex;
std::atomic<bool> found(false);

// Modular inverse using the extended Euclidean algorithm
mp::cpp_int inv(mp::cpp_int a, mp::cpp_int n) {
    mp::cpp_int t = 0, new_t = 1;
    mp::cpp_int r = n, new_r = a;

    while (new_r != 0) {
        mp::cpp_int quotient = r / new_r;
        t = t - quotient * new_t;
        swap(t, new_t);
        r = r - quotient * new_r;
        swap(r, new_r);
    }

    if (r > 1) return 0;  // a is not invertible
    if (t < 0) t = t + n;
    return t;
}

// Point doubling in Jacobian coordinates
Point jacobian_double(Point p) {
    if (get<2>(p) == 0) return make_tuple(0, 0, 0);  // Point at infinity check

    mp::cpp_int x1 = get<0>(p);
    mp::cpp_int y1 = get<1>(p);
    mp::cpp_int z1 = get<2>(p);

    mp::cpp_int y1sq = (y1 * y1) % P;
    mp::cpp_int S = (4 * x1 * y1sq) % P;
    mp::cpp_int M = (3 * x1 * x1 + A * z1 * z1 * z1 * z1) % P;
    mp::cpp_int nx = (M * M - 2 * S) % P;
    if (nx < 0) nx += P;
    mp::cpp_int ny = (M * (S - nx) - 8 * y1sq * y1sq) % P;
    if (ny < 0) ny += P;
    mp::cpp_int nz = (2 * y1 * z1) % P;

    return make_tuple(nx, ny, nz);
}

// Point addition in Jacobian coordinates
Point jacobian_add(Point p, Point q) {
    if (get<2>(p) == 0) return q;
    if (get<2>(q) == 0) return p;

    mp::cpp_int x1 = get<0>(p), y1 = get<1>(p), z1 = get<2>(p);
    mp::cpp_int x2 = get<0>(q), y2 = get<1>(q), z2 = get<2>(q);

    mp::cpp_int z1z1 = (z1 * z1) % P;
    mp::cpp_int z2z2 = (z2 * z2) % P;
    mp::cpp_int u1 = (x1 * z2z2) % P;
    mp::cpp_int u2 = (x2 * z1z1) % P;
    mp::cpp_int s1 = (y1 * z2 * z2z2) % P;
    mp::cpp_int s2 = (y2 * z1 * z1z1) % P;

    if (u1 == u2) {
        if (s1 != s2) return make_tuple(0, 0, 0);
        return jacobian_double(p);
    }

    mp::cpp_int h = (u2 - u1) % P;
    if (h < 0) h += P;
    mp::cpp_int i = (h * h) % P;
    mp::cpp_int j = (h * i) % P;
    mp::cpp_int r = (s2 - s1) % P;
    if (r < 0) r += P;
    mp::cpp_int v = (u1 * i) % P;

    mp::cpp_int nx = (r * r - j - 2 * v) % P;
    if (nx < 0) nx += P;
    mp::cpp_int ny = (r * (v - nx) - s1 * j) % P;
    if (ny < 0) ny += P;
    mp::cpp_int nz = (z1 * z2 * h) % P;

    return make_tuple(nx, ny, nz);
}

// Convert from Jacobian to affine coordinates
Point from_jacobian(Point p) {
    mp::cpp_int x = get<0>(p), y = get<1>(p), z = get<2>(p);
    if (z == 0) return make_tuple(0, 0, 0);  // Point at infinity check
    mp::cpp_int z_inv = inv(z, P);
    mp::cpp_int z_inv2 = (z_inv * z_inv) % P;
    mp::cpp_int z_inv3 = (z_inv2 * z_inv) % P;
    mp::cpp_int affine_x = (x * z_inv2) % P;
    if (affine_x < 0) affine_x += P;
    mp::cpp_int affine_y = (y * z_inv3) % P;
    if (affine_y < 0) affine_y += P;
    return make_tuple(affine_x, affine_y, 1);
}

// Scalar multiplication using double-and-add method
Point jacobian_multiply(Point a, mp::cpp_int n) {
    if (n == 0) return make_tuple(0, 0, 0);
    if (n == 1) return a;

    Point result = make_tuple(0, 0, 0);
    Point addend = a;

    while (n > 0) {
        if (n % 2 == 1) {
            result = jacobian_add(result, addend);
        }
        addend = jacobian_double(addend);
        n /= 2;
    }

    return result;
}

// generate a random cpp_int number between a range
mp::cpp_int generateRandomCppInt(const mp::cpp_int& lowerBound, const mp::cpp_int& upperBound) {
    std::random_device rd;
    std::mt19937_64 gen(rd());

    // Calculate the difference between upper and lower bounds
    mp::cpp_int range = upperBound - lowerBound;

    // Convert the range to a string for length
    std::string rangeStr = range.str();

    // Generate a random number with a similar length as the range
    mp::cpp_int randomNumber = 0;
    for (size_t i = 0; i < rangeStr.size(); ++i) {
        std::uniform_int_distribution<> dis(0, 9);
        randomNumber = randomNumber * 10 + dis(gen);
    }

    // Ensure the random number is within the range
    randomNumber = lowerBound + (randomNumber % range);

    return randomNumber;
}

std::string cppIntToHexString(const mp::cpp_int& value) {
    std::stringstream ss;
    ss << std::hex << value;
    return ss.str();
}

std::vector<unsigned char> hexStringToByteArray(const std::string& hex) {
    std::vector<unsigned char> bytes;
    bytes.reserve(hex.length() / 2);
    for (size_t i = 0; i < hex.length(); i += 2) {
        unsigned int byte;
        std::stringstream ss;
        ss << std::hex << hex.substr(i, 2);
        ss >> byte;
        bytes.push_back(static_cast<unsigned char>(byte));
    }
    return bytes;
}

std::string sha256(const std::vector<unsigned char>& data) {
    unsigned char hash[SHA256_DIGEST_LENGTH];
    SHA256_CTX sha256;
    SHA256_Init(&sha256);
    SHA256_Update(&sha256, data.data(), data.size());
    SHA256_Final(hash, &sha256);

    std::stringstream ss;
    for (int i = 0; i < SHA256_DIGEST_LENGTH; ++i) {
        ss << std::hex << std::setw(2) << std::setfill('0') << (int)hash[i];
    }
    return ss.str();
}

std::string ripemd160(const std::vector<unsigned char>& data) {
    unsigned char hash[RIPEMD160_DIGEST_LENGTH];
    RIPEMD160_CTX ripemd160;
    RIPEMD160_Init(&ripemd160);
    RIPEMD160_Update(&ripemd160, data.data(), data.size());
    RIPEMD160_Final(hash, &ripemd160);
    std::stringstream ss;
    for (int i = 0; i < RIPEMD160_DIGEST_LENGTH; ++i) {
        ss << std::hex << std::setw(2) << std::setfill('0') << (int)hash[i];
    }
    return ss.str();
}

std::string base58encode(const std::string& input) {
    static const char* pszBase58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    mp::cpp_int x("0x" + input);
    std::string result;
    result.reserve(input.size());

    while (x > 0) {
        int remainder = static_cast<int>(x % 58);
        x /= 58;
        result = pszBase58[remainder] + result;
    }

    for (const char& c : input) {
        if (c == '0') {
            result = '1' + result;
        }
        else {
            break;
        }
    }

    return result;
}

std::string getAddress(const std::string& pubkeyHex) {
    // Convert hex string to byte array
    std::vector<unsigned char> pubkeyBytes = hexStringToByteArray(pubkeyHex);

    // Step 1: Compute SHA-256 hash of the public key
    std::string sha256Hash = sha256(pubkeyBytes);
    ///std::cout << "SHA-256 Hash: " << sha256Hash << std::endl;

    // Convert SHA-256 hash string back to byte array
    std::vector<unsigned char> sha256Bytes = hexStringToByteArray(sha256Hash);

    // Step 2: Compute RIPEMD-160 hash of the SHA-256 hash
    std::string ripemd160Hash = ripemd160(sha256Bytes);
    ///std::cout << "RIPEMD-160 Hash: " << ripemd160Hash << std::endl;

    // Step 3: Add Bitcoin network prefix (0x00 for Mainnet)
    std::string extendedHash = "00" + ripemd160Hash;

    // Convert extended hash string back to byte array
    std::vector<unsigned char> extendedBytes = hexStringToByteArray(extendedHash);

    // Step 4: Compute double SHA-256 hash of the extended hash
    std::string checksum = sha256(hexStringToByteArray(sha256(extendedBytes))).substr(0, 8);
    ///std::cout << "Checksum: " << checksum << std::endl;

    // Step 5: Concatenate the extended hash and checksum
    std::string binaryAddress = extendedHash + checksum;

    // Step 6: Convert the binary address to Base58
    return base58encode(binaryAddress);
}

mp::cpp_int hexToDecimal(const std::string& hexString) {
    mp::cpp_int decimalValue;
    std::stringstream hexStream;
    hexStream << std::hex << hexString;
    hexStream >> decimalValue;
    return decimalValue;
}

// load Bitcoin addresses from a file into a set
unordered_set<string> loadAddresses(const string& filename) {
    unordered_set<string> addressSet;
    ifstream file(filename);
    string line;
    while (getline(file, line)) {
        addressSet.insert(line);
    }
    return addressSet;
}

// save output to a text file
void saveOutputToFile(const std::string& filename, const std::string& output) {
    std::ofstream outfile(filename, std::ios_base::app);
    if (!outfile.is_open()) {
        std::cerr << "Unable to open file for writing: " << filename << std::endl;
        return;
    }
    outfile << output << std::endl;
}


void workerFunction(mp::cpp_int start_key, mp::cpp_int end_key, const unordered_set<string>& addressSet) {
    while (!found.load()) {
        mp::cpp_int Dec_value = generateRandomCppInt(start_key, end_key);

        std::string hexString = cppIntToHexString(Dec_value);
        mp::cpp_int privateKey("0x" + hexString);

        Point G = make_tuple(Gx, Gy, 1);
        Point Pub = jacobian_multiply(G, privateKey);
        Point affinePub = from_jacobian(Pub);

        mp::cpp_int pub_x = get<0>(affinePub);
        mp::cpp_int pub_y = get<1>(affinePub);

        std::string pubkeyHex = "04" + cppIntToHexString(pub_x) + cppIntToHexString(pub_y);
        std::string bitcoinAddress = getAddress(pubkeyHex).substr(1);

        if (addressSet.find(bitcoinAddress) != addressSet.end()) {
            found.store(true);
            std::string output = bitcoinAddress + " " + hexString;

            saveOutputToFile("output.txt", output); // Save to file

            std::cout << "Private Key: " << hexString << std::endl;
            std::cout << "Public Key (uncompressed): " << pubkeyHex << std::endl;
            std::cout << "Bitcoin Address: " << bitcoinAddress << std::endl;
        }

        // Update the global counter
        counterMutex.lock();
        globalCounter++;
        counterMutex.unlock();
    }
}

// format the number with thousands separators
std::string formatWithThousandsSeparator(long long value) {
    std::string result;
    std::string str = std::to_string(value);
    int count = 0;

    // Insert thousands separator from the end of the string
    for (auto it = str.rbegin(); it != str.rend(); ++it) {
        if (count > 0 && count % 3 == 0) {
            result.push_back('.');
        }
        result.push_back(*it);
        count++;
    }

    std::reverse(result.begin(), result.end());
    return result;
}

void counterThreadFunction(int logDelay) {
    while (!found.load()) {
        std::this_thread::sleep_for(std::chrono::seconds(logDelay));

        long long count = globalCounter.load();
        std::string formattedCount = formatWithThousandsSeparator(count);

        std::cout << "Total checked: " << formattedCount << std::endl;
    }
}

int main() {
    unordered_set<string> addressSet = loadAddresses("addr.txt");
    std::cout << "Addresses loaded." << std::endl;
    std::cout << " " << std::endl;

    std::string Start_key;
    std::cout << "Start key Range: ";
    std::getline(std::cin, Start_key);

    std::string End_key;
    std::cout << "End key Range: ";
    std::getline(std::cin, End_key);

    if (Start_key.empty()) {
        Start_key = "0x0000000000000000000000000000000000000000000000000000000000000001";
    }

    if (End_key.empty()) {
        End_key = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140";
    }

    int Log_Delay = 30;
    std::string input;

    std::cout << "Log Delay seconds (default is 30 seconds): ";

    std::getline(std::cin, input);

    if (!input.empty()) {
        try {
            // Convert input to integer
            Log_Delay = std::stoi(input);
        }
        catch (const std::invalid_argument& e) {
            // Handle the case where the input is not a valid integer
            std::cout << "Invalid input. Using default value of 30 seconds." << std::endl;
        }
        catch (const std::out_of_range& e) {
            // Handle the case where the input is out of range for an int
            std::cout << "Input out of range. Using default value of 30 seconds." << std::endl;
        }
    }

    std::cout << "Log Delay set to: " << Log_Delay << " seconds." << std::endl;


    mp::cpp_int decimalValue_Start_key = hexToDecimal(Start_key);
    mp::cpp_int decimalValue_End_key = hexToDecimal(End_key);

    int numThreads = 1; // Default value
    std::string input_numThreads;

    std::cout << "Enter the number of threads (default is 1 thread): ";

    std::getline(std::cin, input_numThreads);

    if (!input_numThreads.empty()) {
        try {
            // Convert input to integer
            numThreads = std::stoi(input_numThreads);

            // Check if the number of threads is valid
            if (numThreads <= 0) {
                std::cerr << "Invalid number of threads. Using default value of 1." << std::endl;
                numThreads = 1;
            }
        }
        catch (const std::invalid_argument& e) {
            std::cerr << "Invalid input. Using default value of 1." << std::endl;
        }
        catch (const std::out_of_range& e) {
            std::cerr << "Input out of range. Using default value of 1." << std::endl;
        }
    }

    std::cout << "Num Threads set to: " << numThreads << std::endl;

    std::cout << "Running..." << std::endl;
    std::cout << " " << std::endl;

    std::vector<std::thread> threads;

    std::thread counterThread(counterThreadFunction, Log_Delay);

    for (int i = 0; i < numThreads; ++i) {
        threads.emplace_back(workerFunction, decimalValue_Start_key, decimalValue_End_key, std::ref(addressSet));
    }

    for (auto& t : threads) {
        t.join();
    }

    found.store(true);
    counterThread.join();

    return 0;
}