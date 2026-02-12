# CFLAGS = -std=c++17 -pg -O3 -DNDEBUG -Wall -Wextra -Wno-sign-compare -Wno-unused-variable -Wno-unused-parameter
# CFLAGS = -std=c++17 -O3 -DNDEBUG -Wall -Wextra -Wno-sign-compare -Wno-unused-variable -Wno-unused-parameter
#CFLAGS = -std=c++17 -O3 -g -Wall -Wextra -Wno-sign-compare -Wno-unused-variable -Wno-unused-parameter
CFLAGS = -std=c++17 -O0 -g -Wall -Wextra -Wno-sign-compare

# .cc files with a main are included here
MAIN_SRCS =             \
main.cpp                \

# .cc files with a main are *not* included here
NO_MAIN_SRCS =           \
../Zp.cpp                \
../Global.cpp            \

NO_MAIN_OBJS = $(addsuffix .o,   $(basename $(NO_MAIN_SRCS) .cc))
MAIN_OBJS    = $(addsuffix .o,   $(basename    $(MAIN_SRCS) .cc))
EXES         = $(addsuffix .exe, $(basename    $(MAIN_SRCS) .cc))

all: $(EXES)

%.exe: %.o $(NO_MAIN_OBJS)
	g++ $(CFLAGS) -o $*.exe $*.o $(NO_MAIN_OBJS) -lgmpxx -lgmp

%.o: %.cc
	g++ $(CFLAGS) -o $*.o -c $*.cc

clean:
	rm -rf $(EXES) $(MAIN_OBJS) $(NO_MAIN_OBJS)  \

depend:
	makedepend -Y -- $(CXXFLAGS) -- $(MAIN_SRCS) $(NO_MAIN_SRCS)
# DO NOT DELETE

main.o: ../Square_rooter.hpp ../Zp.hpp ../Global.hpp ../Propagator.hpp
main.o: ../Monomial.hpp ../Context.hpp ../Polynomial.hpp
../Zp.o: ../Zp.hpp ../Global.hpp
../Global.o: ../Global.hpp
