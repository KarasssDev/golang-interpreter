package main;

func fib(n int) int {
	if (n == 0) {
		return 0;
	}
	if (n == 1) {
		return 1;
	}
	return fib(n - 1) + fib(n - 2);
}

func fac(n int) int {
	if (n == 0) {
		return 1;
	}
	return n * fac(n - 1);
}

func f1(n int) int {
	if (n == 0) {
		return 1;
	}
	return f1(n - 1) + f2(n - 1);
}

func f2(n int) int {
	if (n == 0) {
		return 2;
	}
	return f1(n - 1) * f2(n - 1);
}


func main() {
	println(fib(10));
	println(fac(10));
	println(f2(10));
}
