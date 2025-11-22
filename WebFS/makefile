# Makefile

# SDK path
SDK = /usr/share/SDKs/iPhoneOS.sdk

# Compiler and Compiler Flags
CC = clang
CFLAGS = -O2 -Wall -pthread -isysroot $(SDK) -arch arm64 -mios-version-min=12.0

# Source and Target
SRC = webfs.c
TARGET = webfs

# Default Target
all:
	$(CC) $(CFLAGS) -o $(TARGET) $(SRC)

# Clean
clean:
	rm -f $(TARGET)
