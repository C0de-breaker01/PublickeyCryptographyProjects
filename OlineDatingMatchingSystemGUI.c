#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <windows.h>
#include <openssl/bn.h>
#include <openssl/sha.h>
#include <openssl/rand.h>
// GUI相关定义
#define ID_ACCEPT_A 1001
#define ID_REJECT_A 1002
#define ID_ACCEPT_B 1003
#define ID_REJECT_B 1004
#define ID_SUBMIT_A 1005
#define ID_SUBMIT_B 1006
// 日志相关定义
#define LOG_FILE_ALICE "alice_log.txt"
#define LOG_FILE_BOB "bob_log.txt"
#define LOG_FILE_SYSTEM "system_log.txt"
// 密钥生成和加密相关定义
#define MAX_BITS 512
#define MAX_STRING_LENGTH 8192  // 最大字符串长度
#define LOW_LEVEL_PRIMALITY_TEST_BITS 512  // 低位试除法素性检验
#define BLOCK_SIZE 128  // 每块字节数（确保m < q）
#define MILLER_RABIN_ITERATIONS 20  // Miller-Rabin测试迭代次数
#define HEX_OR_DECIMAL 0  // 十六进制(1)或十进制(0)格式
// 公共参数结构体
typedef struct {
    BIGNUM *p;
    BIGNUM *g;
    BIGNUM *q; // q = (p-1)/2
} Params;
// 用户结构体
typedef struct {
    BIGNUM *dh_priv;   // DH私钥x
    BIGNUM *dh_pub;    // DH公钥y = g^x mod p
    BIGNUM *shared_key;// 共享密钥k
    BIGNUM *eg_priv;   // ElGamal私钥x'
    int choice;        // 用户选择: 1=接受, 0=拒绝
    BIGNUM *c1, *c2;   // 加密选择后的密文
    BIGNUM *result;    // 解密后的匹配结果
} User;
// 全局变量
HWND hWndA, hWndB;
HWND hEditInfoA, hEditInfoB;
HWND hResultA, hResultB;
HWND hSubmitA, hSubmitB;  // 添加提交按钮的句柄
HWND hEncryptedInfoA, hEncryptedInfoB;  // 显示加密信息的控件
int choiceA = -1, choiceB = -1;
int submittedA = 0, submittedB = 0;  // 添加提交状态标志
char infoA[256] = "";
char infoB[256] = "";
int matching_completed = 0;
int match_result = 0;
// 全局参数和用户状态
Params *global_params = NULL;
User userA_global = {0}, userB_global = {0};
BIGNUM *platform_C1 = NULL, *platform_C2 = NULL;
// 声明函数
BIGNUM* generate_large_number(int bits);
int is_prime(BIGNUM *n, int iterations);
BIGNUM* generate_safe_prime(int bits);
BIGNUM* find_generator(BIGNUM *p);
void write_log(const char* filename, const char* user, const char* message);
void log_alice(const char* message);
void log_bob(const char* message);
void log_system(const char* message);
// 数字格式转换函数
char* bignum_to_string(BIGNUM *bn) {
    if (!bn) return NULL;
    if (HEX_OR_DECIMAL == 1) {
        return BN_bn2hex(bn);  // 十六进制格式
    } else {
        return BN_bn2dec(bn);  // 十进制格式
    }
}
// 释放数字字符串内存的辅助函数
void free_bignum_string(char *str) {
    if (str) {
        OPENSSL_free(str);
    }
}
// 生成大数
BIGNUM* generate_large_number(int bits) {
    BIGNUM *num = BN_new();
    BN_rand(num, bits, 0, 0);  // 生成一个bits位的随机数
    return num;
}
// Miller-Rabin素性测试
int is_prime(BIGNUM *n, int iterations) {
    BIGNUM *two = BN_new();
    BN_set_word(two, 2);
    if (BN_cmp(n, two) < 0) { BN_free(two); return 0; }
    if (BN_cmp(n, two) == 0) { BN_free(two); return 1; }
    if (!BN_is_odd(n)) { BN_free(two); return 0; }
    BN_CTX *ctx = BN_CTX_new();
    BIGNUM *a = BN_new();
    BIGNUM *d = BN_new();
    BIGNUM *n_minus_1 = BN_new();
    BIGNUM *x = BN_new();
    int result = 1;
    // n - 1
    BN_sub(n_minus_1, n, BN_value_one());
    // d = n - 1
    BN_copy(d, n_minus_1);
    // 将d分解为2^r * d'，其中d'是奇数
    int r = 0;
    while (!BN_is_odd(d)) {
        BN_rshift1(d, d);
        r++;
    }
    for (int i = 0; i < iterations; i++) {
        // 生成 [2, n-2] 范围的随机数
        do {
            BN_rand_range(a, n_minus_1);
        } while (BN_cmp(a, two) < 0);
        // x = a^d mod n
        BN_mod_exp(x, a, d, n, ctx);
        if (BN_is_one(x) || BN_cmp(x, n_minus_1) == 0) continue;
        int passed = 0;
        for (int j = 0; j < r - 1; j++) {
            // x = x^2 mod n
            BN_mod_sqr(x, x, n, ctx);
            if (BN_is_one(x)) {
                result = 0;
                goto cleanup;
            }
            if (BN_cmp(x, n_minus_1) == 0) {
                passed = 1;
                break;
            }
        }
        if (!passed) {
            result = 0;
            goto cleanup;
        }
    }
    cleanup:
        BN_free(a);
        BN_free(d);
        BN_free(n_minus_1);
        BN_free(x);
        BN_CTX_free(ctx);
        BN_free(two);
    return result;
}
// 生成大素数（安全素数） p = 2q + 1，其中p和q都是素数
BIGNUM* generate_safe_prime(int bits) {
    BIGNUM *p = BN_new();
    BIGNUM *q = BN_new();
    BIGNUM *temp = BN_new();
    BN_CTX *ctx = BN_CTX_new();
    char *p_str = NULL;
    char *q_str = NULL;
    char log_buffer[1024];
    do {
        // 生成候选素数q（约为 bits-1 位）
        BN_free(q);
        q = generate_large_number(bits - 1);
        // 确保q是奇数且为素数
        if (!BN_is_odd(q)) {
            BN_add(q, q, BN_value_one());
        }
        // 检验q是否为素数
        if (!is_prime(q, MILLER_RABIN_ITERATIONS)) {
            continue;
        }
        // 计算 p = 2q + 1
        BN_lshift1(temp, q);  // temp = 2*q
        BN_add(p, temp, BN_value_one());
        // 验证p也是素数
        if (is_prime(p, MILLER_RABIN_ITERATIONS)) {
            // 记录生成的安全素数信息
            p_str = bignum_to_string(p);
            q_str = bignum_to_string(q);
            log_system("Safe prime generated successfully");
            snprintf(log_buffer, sizeof(log_buffer), "p = %s", p_str);
            log_system(log_buffer);
            snprintf(log_buffer, sizeof(log_buffer), "q = (p-1)/2 = %s", q_str);
            log_system(log_buffer);
            snprintf(log_buffer, sizeof(log_buffer), "Verification: p = 2q + 1 = 2*%s + 1", q_str);
            log_system(log_buffer);
            // 验证q是素数
            if (is_prime(q, MILLER_RABIN_ITERATIONS)) {
                log_system("Verification passed: q is prime");
            } else {
                log_system("Verification failed: q is not prime");
            }
            free_bignum_string(p_str);
            free_bignum_string(q_str);
            break;
        }
    } while (1);
    BN_free(q);
    BN_free(temp);
    BN_CTX_free(ctx);
    return p;
}
// 生成生成元g（模p的原根）
BIGNUM* find_generator(BIGNUM *p) {
    BN_CTX *ctx = BN_CTX_new();
    BIGNUM *g = BN_new();
    BIGNUM *q = BN_new();  // q = (p-1)/2，使用阶为q的生成元满足DDH条件
    BIGNUM *tmp = BN_new();
    // 计算q = (p-1)/2
    BN_sub(q, p, BN_value_one()); // q = p-1
    BN_rshift1(q, q);             // q = (p-1)/2
    // 随机选择g直到满足条件：g^q mod p != 1
    do {
        BN_rand_range(g, p);  // 0 <= g < p
        if (BN_is_zero(g)) continue;
        BN_mod_exp(tmp, g, q, p, ctx);
    } while (BN_is_one(tmp));
    BN_free(q);
    BN_free(tmp);
    BN_CTX_free(ctx);
    return g;
}
// 生成公共参数
Params* generate_params(void) {
    Params *params = malloc(sizeof(Params));
    if (!params) {
        log_system("错误：参数结构内存分配失败");
        return NULL;
    }
    // 初始化BIGNUM指针
    params->p = NULL;
    params->g = NULL;
    params->q = NULL;
    // 生成安全素数，最多重试5次
    int retry_count = 0;
    const int max_retries = 5;
    char log_buffer[1024];
    while (retry_count < max_retries) {
        params->p = generate_safe_prime(MAX_BITS);  // 生成安全素数
        if (params->p) {
            // 计算q = (p-1)/2
            params->q = BN_new();
            if (!params->q) {
                log_system("错误：q的内存分配失败");
                BN_free(params->p);
                free(params);
                return NULL;
            }
            BN_sub(params->q, params->p, BN_value_one());
            BN_rshift1(params->q, params->q); // q = (p-1)/2
            // 验证q确实是素数（安全素数的特性）
            if (is_prime(params->q, MILLER_RABIN_ITERATIONS)) {
                char *p_str = bignum_to_string(params->p);
                char *q_str = bignum_to_string(params->q);
                log_system("安全素数生成成功");
                snprintf(log_buffer, sizeof(log_buffer), "p = %s", p_str);
                log_system(log_buffer);
                snprintf(log_buffer, sizeof(log_buffer), "q = (p-1)/2 = %s", q_str);
                log_system(log_buffer);
                log_system("验证通过：q是素数");
                free_bignum_string(p_str);
                free_bignum_string(q_str);
                break;
            } else {
                char *q_str = bignum_to_string(params->q);
                snprintf(log_buffer, sizeof(log_buffer), "错误：q = %s 不是素数，正在重新生成", q_str);
                log_system(log_buffer);
                free_bignum_string(q_str);
                BN_free(params->p);
                BN_free(params->q);
                params->p = NULL;
                params->q = NULL;
            }
        }
        retry_count++;
        if (retry_count < max_retries) {
            snprintf(log_buffer, sizeof(log_buffer), "安全素数生成失败，正在重新尝试... (%d/%d)", retry_count, max_retries);
            log_system(log_buffer);
        }
    }
    if (!params->p || !params->q) {
        log_system("错误：安全素数生成失败，无法初始化参数");
        if (params->p) BN_free(params->p);
        if (params->q) BN_free(params->q);
        free(params);
        return NULL;
    }
    params->g = find_generator(params->p);
    if (!params->g) {
        log_system("错误：生成元查找失败");
        BN_free(params->p);
        BN_free(params->q);
        free(params);
        return NULL;
    }
    return params;
}
// 从共享密钥派生ElGamal私钥
void derive_eg_priv(User *user, BIGNUM *q) {
    unsigned char hash[SHA256_DIGEST_LENGTH];
    unsigned char *key_bytes = malloc(BN_num_bytes(user->shared_key));
    int len = BN_bn2bin(user->shared_key, key_bytes);
    SHA256(key_bytes, len, hash);
    BN_bin2bn(hash, SHA256_DIGEST_LENGTH, user->eg_priv);
    BN_CTX *ctx = BN_CTX_new();
    BN_mod(user->eg_priv, user->eg_priv, q, ctx); // x' = H(k) mod q
    BN_CTX_free(ctx);
    free(key_bytes);
}
// 加密用户选择
void encrypt_choice(User *user, Params *params) {
    BN_CTX *ctx = BN_CTX_new();
    BIGNUM *k_enc = BN_new();
    BIGNUM *h = BN_new();
    BIGNUM *s = BN_new();
    BIGNUM *M = BN_new();
    // 计算公钥 h = g^(x') mod p
    BN_mod_exp(h, params->g, user->eg_priv, params->p, ctx);
    // 随机指数 k_enc ∈ [1, q-1]
    BN_rand_range(k_enc, params->q);
    // c1 = g^(k_enc) mod p
    user->c1 = BN_new();
    BN_mod_exp(user->c1, params->g, k_enc, params->p, ctx);
    // s = h^(k_enc) mod p
    BN_mod_exp(s, h, k_enc, params->p, ctx);
    if (user->choice == 1) { // 接受: 加密1
        BN_one(M);
    } else { // 拒绝: 加密随机群元素
        BIGNUM *r = BN_new();
        BN_rand_range(r, params->q);
        BN_mod_exp(M, params->g, r, params->p, ctx); // M = g^r mod p
        BN_free(r);
    }
    // c2 = M * s mod p
    user->c2 = BN_new();
    BN_mod_mul(user->c2, M, s, params->p, ctx);
    // 清理
    BN_free(k_enc);
    BN_free(h);
    BN_free(s);
    BN_free(M);
    BN_CTX_free(ctx);
}
// 平台进行同态运算
void homomorphic_operation(BIGNUM **C1, BIGNUM **C2, User *userA, User *userB, Params *params) {
    BN_CTX *ctx = BN_CTX_new();
    BIGNUM *c1_total = BN_new();
    BIGNUM *c2_total = BN_new();
    BIGNUM *r = BN_new();
    // 同态乘法: c1_total = c1A * c1B mod p
    BN_mod_mul(c1_total, userA->c1, userB->c1, params->p, ctx);
    // 同态乘法: c2_total = c2A * c2B mod p
    BN_mod_mul(c2_total, userA->c2, userB->c2, params->p, ctx);
    // 再随机化: 选择随机指数 r ∈ [1, q-1]
    BN_rand_range(r, params->q);
    // C1 = c1_total^r mod p
    *C1 = BN_new();
    BN_mod_exp(*C1, c1_total, r, params->p, ctx);
    // C2 = c2_total^r mod p
    *C2 = BN_new();
    BN_mod_exp(*C2, c2_total, r, params->p, ctx);
    // 清理
    BN_free(c1_total);
    BN_free(c2_total);
    BN_free(r);
    BN_CTX_free(ctx);
}
// 用户解密匹配结果
void decrypt_result(User *user, BIGNUM *C1, BIGNUM *C2, Params *params) {
    BN_CTX *ctx = BN_CTX_new();
    BIGNUM *s = BN_new();
    BIGNUM *s_inv = BN_new();
    // s = C1^(x') mod p
    BN_mod_exp(s, C1, user->eg_priv, params->p, ctx);
    // s_inv = s^(-1) mod p
    BN_mod_inverse(s_inv, s, params->p, ctx);
    // result = C2 * s_inv mod p
    user->result = BN_new();
    BN_mod_mul(user->result, C2, s_inv, params->p, ctx);
    // 清理
    BN_free(s);
    BN_free(s_inv);
    BN_CTX_free(ctx);
}
// 平台端：初始化公共参数
void platform_initialize() {
    log_system("平台端：开始初始化公共参数");
    global_params = generate_params();
    if (!global_params) {
        log_system("错误：公共参数生成失败");
        return;
    }
    // 记录公共参数到系统日志
    char *p_str = bignum_to_string(global_params->p);
    char *g_str = bignum_to_string(global_params->g);
    char *q_str = bignum_to_string(global_params->q);
    char param_log[2048];
    const char* format_type = (HEX_OR_DECIMAL == 1) ? "十六进制" : "十进制";
    sprintf(param_log, "公共参数(%s) p: %s", format_type, p_str ? p_str : "NULL");
    log_system(param_log);
    sprintf(param_log, "生成元(%s) g: %s", format_type, g_str ? g_str : "NULL");
    log_system(param_log);
    sprintf(param_log, "阶(%s) q: %s", format_type, q_str ? q_str : "NULL");
    log_system(param_log);
    free_bignum_string(p_str);
    free_bignum_string(g_str);
    free_bignum_string(q_str);
    log_system("平台端：公共参数初始化完成");
}
// 用户端：生成密钥对和加密选择
void user_generate_and_encrypt(User *user, int choice, const char* user_name) {
    char log_msg[1024];
    sprintf(log_msg, "%s开始生成密钥对", user_name);
    if (strcmp(user_name, "Alice") == 0) {
        log_alice("开始生成DH密钥对");
    } else {
        log_bob("开始生成DH密钥对");
    }
    user->choice = choice;
    BN_CTX *ctx = BN_CTX_new();
    // 生成DH密钥对
    user->dh_priv = BN_new();
    user->dh_pub = BN_new();
    BN_rand_range(user->dh_priv, global_params->q);
    BN_mod_exp(user->dh_pub, global_params->g, user->dh_priv, global_params->p, ctx);
    // 记录密钥信息
    char *priv_hex = bignum_to_string(user->dh_priv);
    char *pub_hex = bignum_to_string(user->dh_pub);
    const char* format_type = (HEX_OR_DECIMAL == 1) ? "十六进制" : "十进制";
    sprintf(log_msg, "生成DH私钥(%s): %s", format_type, priv_hex ? priv_hex : "NULL");
    if (strcmp(user_name, "Alice") == 0) {
        log_alice(log_msg);
    } else {
        log_bob(log_msg);
    }
    sprintf(log_msg, "计算DH公钥(%s): %s", format_type, pub_hex ? pub_hex : "NULL");
    if (strcmp(user_name, "Alice") == 0) {
        log_alice(log_msg);
    } else {
        log_bob(log_msg);
    }
    free_bignum_string(priv_hex);
    free_bignum_string(pub_hex);
    BN_CTX_free(ctx);
}
// 用户端：计算共享密钥并加密选择
void user_compute_shared_and_encrypt(User *user, User *other_user, const char* user_name) {
    char log_msg[1024];
    BN_CTX *ctx = BN_CTX_new();
    // 计算共享密钥
    user->shared_key = BN_new();
    BN_mod_exp(user->shared_key, other_user->dh_pub, user->dh_priv, global_params->p, ctx);
    char *shared_hex = bignum_to_string(user->shared_key);
    const char* format_type = (HEX_OR_DECIMAL == 1) ? "十六进制" : "十进制";
    sprintf(log_msg, "计算得到共享密钥(%s): %s", format_type, shared_hex ? shared_hex : "NULL");
    if (strcmp(user_name, "Alice") == 0) {
        log_alice(log_msg);
    } else {
        log_bob(log_msg);
    }
    free_bignum_string(shared_hex);
    // 派生ElGamal私钥
    user->eg_priv = BN_new();
    derive_eg_priv(user, global_params->q);
    char *eg_hex = bignum_to_string(user->eg_priv);
    sprintf(log_msg, "派生ElGamal私钥(%s): %s", format_type, eg_hex ? eg_hex : "NULL");
    if (strcmp(user_name, "Alice") == 0) {
        log_alice(log_msg);
    } else {
        log_bob(log_msg);
    }
    free_bignum_string(eg_hex);
    // 加密用户选择
    encrypt_choice(user, global_params);
    char *c1_hex = bignum_to_string(user->c1);
    char *c2_hex = bignum_to_string(user->c2);
    sprintf(log_msg, "加密选择(%s) - C1(%s): %s", user->choice ? "接受" : "拒绝", format_type, c1_hex ? c1_hex : "NULL");
    if (strcmp(user_name, "Alice") == 0) {
        log_alice(log_msg);
    } else {
        log_bob(log_msg);
    }
    sprintf(log_msg, "加密选择(%s) - C2(%s): %s", user->choice ? "接受" : "拒绝", format_type, c2_hex ? c2_hex : "NULL");
    if (strcmp(user_name, "Alice") == 0) {
        log_alice(log_msg);
    } else {
        log_bob(log_msg);
    }
    free_bignum_string(c1_hex);
    free_bignum_string(c2_hex);
    BN_CTX_free(ctx);
}
// 平台端：执行同态运算
void platform_homomorphic_computation() {
    log_system("平台端：开始执行同态运算");
    // 安全检查：验证输入参数
    if (!userA_global.c1 || !userA_global.c2 || !userB_global.c1 || !userB_global.c2) {
        log_system("错误：密文数据不完整，同态运算终止");
        return;
    }
    // 记录收到的密文
    char *alice_c1_hex = bignum_to_string(userA_global.c1);
    char *alice_c2_hex = bignum_to_string(userA_global.c2);
    char *bob_c1_hex = bignum_to_string(userB_global.c1);
    char *bob_c2_hex = bignum_to_string(userB_global.c2);
    // 动态分配缓冲区避免栈溢出
    char *log_msg = malloc(2048);
    if (!log_msg) {
        log_system("错误：内存分配失败");
        goto cleanup_initial;
    }
    const char* format_type = (HEX_OR_DECIMAL == 1) ? "十六进制" : "十进制";
    sprintf(log_msg, "收到Alice密文(%s) - C1: %s", format_type, alice_c1_hex ? alice_c1_hex : "NULL");
    log_system(log_msg);
    sprintf(log_msg, "收到Alice密文(%s) - C2: %s", format_type, alice_c2_hex ? alice_c2_hex : "NULL");
    log_system(log_msg);
    sprintf(log_msg, "收到Bob密文(%s) - C1: %s", format_type, bob_c1_hex ? bob_c1_hex : "NULL");
    log_system(log_msg);
    sprintf(log_msg, "收到Bob密文(%s) - C2: %s", format_type, bob_c2_hex ? bob_c2_hex : "NULL");
    log_system(log_msg);
    // 执行同态运算
    homomorphic_operation(&platform_C1, &platform_C2, &userA_global, &userB_global, global_params);
    // 检查同态运算结果
    if (!platform_C1 || !platform_C2) {
        log_system("错误：同态运算失败");
        free(log_msg);
        goto cleanup_initial;
    }
    // 记录同态运算结果
    char *final_c1_hex = bignum_to_string(platform_C1);
    char *final_c2_hex = bignum_to_string(platform_C2);
    sprintf(log_msg, "同态运算结果(%s) - C1: %s", format_type, final_c1_hex ? final_c1_hex : "NULL");
    log_system(log_msg);
    sprintf(log_msg, "同态运算结果(%s) - C2: %s", format_type, final_c2_hex ? final_c2_hex : "NULL");
    log_system(log_msg);
    // 验证随机化后的匹配结果（用于系统日志）
    BIGNUM *test_result = BN_new();
    BN_CTX *ctx = BN_CTX_new();
    BIGNUM *s = BN_new();
    BIGNUM *s_inv = BN_new();
    BIGNUM *one = BN_new();
    if (!test_result || !ctx || !s || !s_inv || !one) {
        log_system("错误：验证过程内存分配失败");
        goto cleanup_verification;
    }
    // 使用Alice的私钥解密验证结果
    BN_mod_exp(s, platform_C1, userA_global.eg_priv, global_params->p, ctx);
    BN_mod_inverse(s_inv, s, global_params->p, ctx);
    BN_mod_mul(test_result, platform_C2, s_inv, global_params->p, ctx);
    // 检查是否为1（匹配成功）
    BN_one(one);
    int platform_match_result = (BN_cmp(test_result, one) == 0) ? 1 : 0;
    char *test_result_hex = bignum_to_string(test_result);
    sprintf(log_msg, "平台验证匹配结果(%s): %s (%s)", format_type, test_result_hex ? test_result_hex : "NULL", platform_match_result ? "匹配成功" : "匹配失败");
    log_system(log_msg);
    free_bignum_string(test_result_hex);
    log_alice("收到平台同态运算结果，准备解密");
    log_bob("收到平台同态运算结果，准备解密");
cleanup_verification:
    // 安全释放内存
    if (test_result) BN_free(test_result);
    if (s) BN_free(s);
    if (s_inv) BN_free(s_inv);
    if (one) BN_free(one);
    if (ctx) BN_CTX_free(ctx);
    OPENSSL_free(final_c1_hex);
    OPENSSL_free(final_c2_hex);
    free(log_msg);
cleanup_initial:
    free_bignum_string(alice_c1_hex);
    free_bignum_string(alice_c2_hex);
    free_bignum_string(bob_c1_hex);
    free_bignum_string(bob_c2_hex);
    log_system("平台端：同态运算完成");
}
// 用户端：解密匹配结果
int user_decrypt_result(User *user, const char* user_name) {
    // 解密结果
    decrypt_result(user, platform_C1, platform_C2, global_params);
    char *result_hex = bignum_to_string(user->result);
    char log_msg[1024];
    const char* format_type = (HEX_OR_DECIMAL == 1) ? "十六进制" : "十进制";
    sprintf(log_msg, "解密得到匹配结果(%s): %s", format_type, result_hex ? result_hex : "NULL");
    if (strcmp(user_name, "Alice") == 0) {
        log_alice(log_msg);
    } else {
        log_bob(log_msg);
    }
    free_bignum_string(result_hex);
    // 验证是否为1（匹配成功）
    BIGNUM *one = BN_new();
    BN_one(one);
    int result = (BN_cmp(user->result, one) == 0) ? 1 : 0;
    BN_free(one);
    if (result) {
        sprintf(log_msg, "%s：匹配成功！", user_name);
    } else {
        sprintf(log_msg, "%s：匹配失败", user_name);
    }
    if (strcmp(user_name, "Alice") == 0) {
        log_alice(log_msg);
    } else {
        log_bob(log_msg);
    }
    return result;
}
// 执行完整匹配协议的函数
int perform_matching_protocol(int choiceA_param, int choiceB_param) {
    log_system("开始执行匹配协议");
    // 1. 平台初始化
    platform_initialize();
    // 2. 用户生成密钥对
    user_generate_and_encrypt(&userA_global, choiceA_param, "Alice");
    user_generate_and_encrypt(&userB_global, choiceB_param, "Bob");
    // 3. 用户计算共享密钥并加密选择
    user_compute_shared_and_encrypt(&userA_global, &userB_global, "Alice");
    user_compute_shared_and_encrypt(&userB_global, &userA_global, "Bob");
    // 4. 平台执行同态运算
    platform_homomorphic_computation();
    // 5. 用户解密结果
    int resultA = user_decrypt_result(&userA_global, "Alice");
    int resultB = user_decrypt_result(&userB_global, "Bob");
    // 6. 验证匹配结果
    int final_result = (resultA && resultB) ? 1 : 0;
    if (final_result) {
        log_system("匹配协议结果: 成功");
    } else {
        log_system("匹配协议结果: 失败");
    }
    log_system("匹配协议执行完成");
    return final_result;
}
// 释放资源的统一函数
void cleanup_resources(void) {
    // 释放用户A的资源
    if (userA_global.dh_priv) BN_free(userA_global.dh_priv);
    if (userA_global.dh_pub) BN_free(userA_global.dh_pub);
    if (userA_global.shared_key) BN_free(userA_global.shared_key);
    if (userA_global.eg_priv) BN_free(userA_global.eg_priv);
    if (userA_global.c1) BN_free(userA_global.c1);
    if (userA_global.c2) BN_free(userA_global.c2);
    if (userA_global.result) BN_free(userA_global.result);
    // 释放用户B的资源
    if (userB_global.dh_priv) BN_free(userB_global.dh_priv);
    if (userB_global.dh_pub) BN_free(userB_global.dh_pub);
    if (userB_global.shared_key) BN_free(userB_global.shared_key);
    if (userB_global.eg_priv) BN_free(userB_global.eg_priv);
    if (userB_global.c1) BN_free(userB_global.c1);
    if (userB_global.c2) BN_free(userB_global.c2);
    if (userB_global.result) BN_free(userB_global.result);
    // 释放平台资源
    if (platform_C1) BN_free(platform_C1);
    if (platform_C2) BN_free(platform_C2);
    // 释放全局参数
    if (global_params) {
        if (global_params->p) BN_free(global_params->p);
        if (global_params->g) BN_free(global_params->g);
        if (global_params->q) BN_free(global_params->q);
        free(global_params);
        global_params = NULL;
    }
    // 重置全局状态
    memset(&userA_global, 0, sizeof(User));
    memset(&userB_global, 0, sizeof(User));
    platform_C1 = NULL;
    platform_C2 = NULL;
    choiceA = -1;
    choiceB = -1;
    submittedA = 0;
    submittedB = 0;
    matching_completed = 0;
    match_result = 0;
    log_system("系统资源已清理完成");
}
// 输入验证函数
int validate_input(const char* input) {
    if (!input || strlen(input) == 0) {
        return 0; // 空输入无效
    }
    if (strlen(input) > 255) {
        return 0; // 输入过长
    }
    // 检查是否包含非法字符
    for (int i = 0; input[i]; i++) {
        if (input[i] < 32 || input[i] > 126) {
            if (input[i] != '\r' && input[i] != '\n' && input[i] != '\t') {
                return 0; // 包含非可打印字符
            }
        }
    }
    return 1; // 输入有效
}
// 日志函数
void write_log(const char* filename, const char* user, const char* message) {
    if (!filename || !user || !message) {
        return; // 参数检查
    }
    FILE* file = fopen(filename, "a");
    if (file) {
        SYSTEMTIME st;
        GetSystemTime(&st);
        // 使用安全的格式字符串
        int result = fprintf(file, "[%04d-%02d-%02d %02d:%02d:%02d] %s: %s\n", st.wYear, st.wMonth, st.wDay, st.wHour, st.wMinute, st.wSecond,user, message);
        if (result < 0) {
            // 写入失败处理
            fclose(file);
            return;
        }
        fclose(file);
        // 确保日志文件不会过大（简单的日志轮转）
        file = fopen(filename, "r");
        if (file) {
            fseek(file, 0, SEEK_END);
            long size = ftell(file);
            fclose(file);
            // 如果文件大于1MB，创建备份并重新开始
            if (size > 1048576) {
                char backup_name[300];
                sprintf(backup_name, "%s.bak", filename);
                rename(filename, backup_name);
            }
        }
    }
}
void log_alice(const char* message) {
    write_log(LOG_FILE_ALICE, "Alice", message);
}
void log_bob(const char* message) {
    write_log(LOG_FILE_BOB, "Bob", message);
}
void log_system(const char* message) {
    write_log(LOG_FILE_SYSTEM, "System", message);
}
// 窗口过程函数
LRESULT CALLBACK WindowProcA(HWND hwnd, UINT uMsg, WPARAM wParam, LPARAM lParam) {
    switch (uMsg) {
        case WM_CREATE:
            CreateWindow("STATIC", "Alice的个人信息:", WS_VISIBLE | WS_CHILD, 10, 10, 150, 20, hwnd, NULL, NULL, NULL);
            hEditInfoA = CreateWindow("EDIT", infoA, WS_VISIBLE | WS_CHILD | WS_BORDER | ES_MULTILINE, 10, 35, 300, 60, hwnd, NULL, NULL, NULL);
            CreateWindow("STATIC", "请选择您的决定:", WS_VISIBLE | WS_CHILD, 10, 105, 150, 20, hwnd, NULL, NULL, NULL);
            CreateWindow("BUTTON", "接受", WS_VISIBLE | WS_CHILD | BS_AUTORADIOBUTTON | WS_GROUP, 10, 130, 80, 25, hwnd, (HMENU)ID_ACCEPT_A, NULL, NULL);
            CreateWindow("BUTTON", "拒绝", WS_VISIBLE | WS_CHILD | BS_AUTORADIOBUTTON, 100, 130, 80, 25, hwnd, (HMENU)ID_REJECT_A, NULL, NULL);
            hSubmitA = CreateWindow("BUTTON", "提交", WS_VISIBLE | WS_CHILD | BS_PUSHBUTTON, 10, 165, 80, 30, hwnd, (HMENU)ID_SUBMIT_A, NULL, NULL);
            CreateWindow("STATIC", "对方加密个人信息:", WS_VISIBLE | WS_CHILD, 10, 205, 150, 20, hwnd, NULL, NULL, NULL);
            hEncryptedInfoA = CreateWindow("EDIT", "", WS_VISIBLE | WS_CHILD | WS_BORDER | ES_MULTILINE | ES_READONLY | WS_VSCROLL, 10, 225, 300, 60, hwnd, NULL, NULL, NULL);
            CreateWindow("STATIC", "匹配结果:", WS_VISIBLE | WS_CHILD, 10, 295, 150, 20, hwnd, NULL, NULL, NULL);
            hResultA = CreateWindow("EDIT", "", WS_VISIBLE | WS_CHILD | WS_BORDER | ES_MULTILINE | ES_READONLY | WS_VSCROLL, 10, 315, 300, 80, hwnd, NULL, NULL, NULL);
            break;
        case WM_COMMAND:
            switch (LOWORD(wParam)) {
                case ID_ACCEPT_A:
                    choiceA = 1;
                    log_alice("选择了接受");
                    break;
                case ID_REJECT_A:
                    choiceA = 0;
                    log_alice("选择了拒绝");
                    break;
                case ID_SUBMIT_A:
                    if (submittedA) {
                        MessageBox(hwnd, "您已经提交过选择，请等待对方提交!", "提示", MB_OK);
                        log_alice("尝试重复提交选择");
                        return 0;
                    }
                    if (choiceA == -1) {
                        MessageBox(hwnd, "请先选择接受或拒绝!", "提示", MB_OK);
                        log_alice("未选择直接提交");
                        return 0;
                    }
                    // 获取并验证输入
                    GetWindowText(hEditInfoA, infoA, sizeof(infoA));
                    if (!validate_input(infoA)) {
                        MessageBox(hwnd, "个人信息输入无效，请检查输入内容!", "输入错误", MB_OK);
                        log_alice("个人信息输入验证失败");
                        return 0;
                    }
                    // 标记为已提交
                    submittedA = 1;
                    SetWindowText(hResultA, "已提交选择，等待对方...");
                    EnableWindow(hSubmitA, FALSE);  // 禁用提交按钮
                    char choice_msg[100];
                    sprintf(choice_msg, "提交了选择: %s", choiceA ? "接受" : "拒绝");
                    log_alice(choice_msg);
                    log_alice("等待对方提交选择");
                    // 初始化平台并生成Alice的密钥
                    if (!global_params) {
                        platform_initialize();
                        if (!global_params) {
                            MessageBox(hwnd, "系统初始化失败!", "错误", MB_OK);
                            log_alice("平台初始化失败");
                            submittedA = 0;
                            EnableWindow(hSubmitA, TRUE);
                            return 0;
                        }
                    }
                    user_generate_and_encrypt(&userA_global, choiceA, "Alice");
                    // 检查是否双方都已提交
                    if (submittedB) {
                        log_alice("对方已提交，开始密钥交换");
                        // 计算共享密钥并加密
                        user_compute_shared_and_encrypt(&userA_global, &userB_global, "Alice");
                        user_compute_shared_and_encrypt(&userB_global, &userA_global, "Bob");
                        // 显示对方的加密信息
                        char *bob_c1_hex = bignum_to_string(userB_global.c1);
                        char *bob_c2_hex = bignum_to_string(userB_global.c2);
                        char *encrypted_info = malloc(1500);
                        if (encrypted_info) {
                            const char* format_type = (HEX_OR_DECIMAL == 1) ? "十六进制" : "十进制";
                            sprintf(encrypted_info, "Bob的加密个人信息(%s):\r\nC1: %.1024s \r\nC2: %.1024s", format_type, bob_c1_hex, bob_c2_hex);
                            SetWindowText(hEncryptedInfoA, encrypted_info);
                            free(encrypted_info);
                        }
                        free_bignum_string(bob_c1_hex);
                        free_bignum_string(bob_c2_hex);
                        // 执行平台同态运算
                        platform_homomorphic_computation();
                        // 解密并显示最终结果
                        matching_completed = 1;
                        int resultA = user_decrypt_result(&userA_global, "Alice");
                        int resultB = user_decrypt_result(&userB_global, "Bob");
                        match_result = (resultA && resultB) ? 1 : 0;
                        char *result_text = malloc(600);
                        if (result_text) {
                            if (match_result) {
                                sprintf(result_text, "匹配成功!\r\n对方信息: %s", infoB);
                                log_alice("匹配成功，可以交换信息");
                            } else {
                                strcpy(result_text, "匹配失败，未能找到共同兴趣。");
                                log_alice("匹配失败，不交换信息");
                            }
                            SetWindowText(hResultA, result_text);
                            free(result_text);
                        }
                        // 更新Bob窗口的结果
                        if (hResultB) {
                            char *result_text_b = malloc(600);
                            if (result_text_b) {
                                if (match_result) {
                                    sprintf(result_text_b, "匹配成功!\r\n对方信息: %s", infoA);
                                } else {
                                    strcpy(result_text_b, "匹配失败，未能找到共同兴趣。");
                                }
                                SetWindowText(hResultB, result_text_b);
                                free(result_text_b);
                            }
                        }
                        // 更新Bob窗口的加密信息显示
                        if (hEncryptedInfoB) {
                            char *alice_c1_hex = bignum_to_string(userA_global.c1);
                            char *alice_c2_hex = bignum_to_string(userA_global.c2);
                            char *encrypted_info_b = malloc(1500);
                            if (encrypted_info_b) {
                                const char* format_type = (HEX_OR_DECIMAL == 1) ? "十六进制" : "十进制";
                                sprintf(encrypted_info_b, "Alice的加密个人信息(%s):\r\nC1: %.1024s \r\nC2: %.1024s", format_type, alice_c1_hex, alice_c2_hex);
                                SetWindowText(hEncryptedInfoB, encrypted_info_b);
                                free(encrypted_info_b);
                            }
                            free_bignum_string(alice_c1_hex);
                            free_bignum_string(alice_c2_hex);
                        }
                    }
                    break;
            }
            break;
        case WM_DESTROY:
            PostQuitMessage(0);
            break;
        default:
            return DefWindowProc(hwnd, uMsg, wParam, lParam);
    }
    return 0;
}
LRESULT CALLBACK WindowProcB(HWND hwnd, UINT uMsg, WPARAM wParam, LPARAM lParam) {
    switch (uMsg) {
        case WM_CREATE:
            CreateWindow("STATIC", "Bob的个人信息:", WS_VISIBLE | WS_CHILD, 10, 10, 150, 20, hwnd, NULL, NULL, NULL);
            hEditInfoB = CreateWindow("EDIT", infoB, WS_VISIBLE | WS_CHILD | WS_BORDER | ES_MULTILINE, 10, 35, 300, 60, hwnd, NULL, NULL, NULL);
            CreateWindow("STATIC", "请选择您的决定:", WS_VISIBLE | WS_CHILD, 10, 105, 150, 20, hwnd, NULL, NULL, NULL);
            CreateWindow("BUTTON", "接受", WS_VISIBLE | WS_CHILD | BS_AUTORADIOBUTTON | WS_GROUP, 10, 130, 80, 25, hwnd, (HMENU)ID_ACCEPT_B, NULL, NULL);
            CreateWindow("BUTTON", "拒绝", WS_VISIBLE | WS_CHILD | BS_AUTORADIOBUTTON, 100, 130, 80, 25, hwnd, (HMENU)ID_REJECT_B, NULL, NULL);
            hSubmitB = CreateWindow("BUTTON", "提交", WS_VISIBLE | WS_CHILD | BS_PUSHBUTTON, 10, 165, 80, 30, hwnd, (HMENU)ID_SUBMIT_B, NULL, NULL);
            CreateWindow("STATIC", "对方加密个人信息:", WS_VISIBLE | WS_CHILD, 10, 205, 150, 20, hwnd, NULL, NULL, NULL);
            hEncryptedInfoB = CreateWindow("EDIT", "", WS_VISIBLE | WS_CHILD | WS_BORDER | ES_MULTILINE | ES_READONLY | WS_VSCROLL, 10, 225, 300, 60, hwnd, NULL, NULL, NULL);
            CreateWindow("STATIC", "匹配结果:", WS_VISIBLE | WS_CHILD, 10, 295, 150, 20, hwnd, NULL, NULL, NULL);
            hResultB = CreateWindow("EDIT", "", WS_VISIBLE | WS_CHILD | WS_BORDER | ES_MULTILINE | ES_READONLY | WS_VSCROLL, 10, 315, 300, 80, hwnd, NULL, NULL, NULL);
            break;
        case WM_COMMAND:
            switch (LOWORD(wParam)) {
                case ID_ACCEPT_B:
                    choiceB = 1;
                    log_bob("选择了接受");
                    break;
                case ID_REJECT_B:
                    choiceB = 0;
                    log_bob("选择了拒绝");
                    break;
                case ID_SUBMIT_B:
                    if (submittedB) {
                        MessageBox(hwnd, "您已经提交过选择，请等待对方提交!", "提示", MB_OK);
                        log_bob("尝试重复提交选择");
                        return 0;
                    }
                    if (choiceB == -1) {
                        MessageBox(hwnd, "请先选择接受或拒绝!", "提示", MB_OK);
                        log_bob("未选择直接提交");
                        return 0;
                    }
                    // 标记为已提交
                    submittedB = 1;
                    GetWindowText(hEditInfoB, infoB, sizeof(infoB));
                    SetWindowText(hResultB, "已提交选择，等待对方...");
                    EnableWindow(hSubmitB, FALSE);  // 禁用提交按钮
                    char choice_msg_b[100];
                    sprintf(choice_msg_b, "提交了选择: %s", choiceB ? "接受" : "拒绝");
                    log_bob(choice_msg_b);
                    log_bob("等待Alice提交选择");
                    // 初始化平台并生成Bob的密钥
                    if (!global_params) {
                        platform_initialize();
                    }
                    user_generate_and_encrypt(&userB_global, choiceB, "Bob");
                    // 检查是否双方都已提交
                    if (submittedA) {
                        log_bob("Alice已提交，开始密钥交换");
                        // 计算共享密钥并加密
                        user_compute_shared_and_encrypt(&userA_global, &userB_global, "Alice");
                        user_compute_shared_and_encrypt(&userB_global, &userA_global, "Bob");
                        // 显示对方的加密信息
                        char *alice_c1_hex = bignum_to_string(userA_global.c1);
                        char *alice_c2_hex = bignum_to_string(userA_global.c2);
                        char encrypted_info[1024];
                        const char* format_type = (HEX_OR_DECIMAL == 1) ? "十六进制" : "十进制";
                        sprintf(encrypted_info, "Alice的加密个人信息(%s):\r\nC1: %.1024s \r\nC2: %.1024s", format_type, alice_c1_hex, alice_c2_hex);
                        SetWindowText(hEncryptedInfoB, encrypted_info);
                        free_bignum_string(alice_c1_hex);
                        free_bignum_string(alice_c2_hex);
                        // 执行平台同态运算
                        platform_homomorphic_computation();
                        // 解密并显示最终结果
                        matching_completed = 1;
                        int resultA = user_decrypt_result(&userA_global, "Alice");
                        int resultB = user_decrypt_result(&userB_global, "Bob");
                        match_result = (resultA && resultB) ? 1 : 0;
                        char result_text[512];
                        if (match_result) {
                            sprintf(result_text, "匹配成功!\r\n对方信息: %s", infoA);
                            log_bob("匹配成功，获得对方信息");
                        } else {
                            strcpy(result_text, "匹配失败，未能找到共同兴趣。");
                            log_bob("匹配失败");
                        }
                        SetWindowText(hResultB, result_text);
                        // 更新Alice窗口
                        if (hResultA) {
                            char result_text_a[512];
                            if (match_result) {
                                sprintf(result_text_a, "匹配成功!\r\n对方信息: %s", infoB);
                            } else {
                                strcpy(result_text_a, "匹配失败，未能找到共同兴趣。");
                            }
                            SetWindowText(hResultA, result_text_a);
                        }
                        // 更新Alice窗口的加密信息显示
                        if (hEncryptedInfoA) {
                            char *bob_c1_hex = bignum_to_string(userB_global.c1);
                            char *bob_c2_hex = bignum_to_string(userB_global.c2);
                            char encrypted_info_a[1024];
                            const char* format_type = (HEX_OR_DECIMAL == 1) ? "十六进制" : "十进制";
                            sprintf(encrypted_info_a, "Bob的加密个人信息(%s):\r\nC1: %.1024s \r\nC2: %.1024s", format_type, bob_c1_hex, bob_c2_hex);
                            SetWindowText(hEncryptedInfoA, encrypted_info_a);
                            free_bignum_string(bob_c1_hex);
                            free_bignum_string(bob_c2_hex);
                        }
                    }
                    break;
            }
            break;
        case WM_DESTROY:
            PostQuitMessage(0);
            break;
        default:
            return DefWindowProc(hwnd, uMsg, wParam, lParam);
    }
    return 0;
}
// 主函数
int WINAPI WinMain(HINSTANCE hInstance, HINSTANCE hPrevInstance, LPSTR lpCmdLine, int nCmdShow) {
    // 初始化日志
    log_system("在线约会匹配系统启动");
    log_alice("用户Alice登录系统");
    log_bob("用户Bob登录系统");
    // 注册窗口类A
    WNDCLASS wcA = {0};
    wcA.lpfnWndProc = WindowProcA;
    wcA.hInstance = hInstance;
    wcA.lpszClassName = "WindowA";
    wcA.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);
    wcA.hCursor = LoadCursor(NULL, IDC_ARROW);
    RegisterClass(&wcA);
    // 注册窗口类B
    WNDCLASS wcB = {0};
    wcB.lpfnWndProc = WindowProcB;
    wcB.hInstance = hInstance;
    wcB.lpszClassName = "WindowB";
    wcB.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);
    wcB.hCursor = LoadCursor(NULL, IDC_ARROW);
    RegisterClass(&wcB);
    // 创建Alice窗口
    hWndA = CreateWindow("WindowA", "Alice - 在线约会匹配系统", WS_OVERLAPPEDWINDOW, 100, 100, 350, 450, NULL, NULL, hInstance, NULL);
    // 创建Bob窗口
    hWndB = CreateWindow("WindowB", "Bob - 在线约会匹配系统", WS_OVERLAPPEDWINDOW, 500, 100, 350, 450, NULL, NULL, hInstance, NULL);
    if (!hWndA || !hWndB) {
        MessageBox(NULL, "窗口创建失败!", "错误", MB_OK);
        log_system("窗口创建失败，程序退出");
        return 1;
    }
    log_system("GUI界面创建成功");
    log_alice("界面已准备就绪");
    log_bob("界面已准备就绪");
    ShowWindow(hWndA, nCmdShow);
    ShowWindow(hWndB, nCmdShow);
    UpdateWindow(hWndA);
    UpdateWindow(hWndB);
    // 消息循环
    MSG msg;
    while (GetMessage(&msg, NULL, 0, 0)) {
        TranslateMessage(&msg);
        DispatchMessage(&msg);
    }
    // 程序退出前清理资源
    cleanup_resources();
    log_system("程序正常退出");
    return msg.wParam;
}
