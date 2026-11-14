// The VM calls only sodium_init() (vm.cpp, init_vm); stubs.cpp defines it.
#pragma once
#ifdef __cplusplus
extern "C" {
#endif
int sodium_init(void);
#ifdef __cplusplus
}
#endif
