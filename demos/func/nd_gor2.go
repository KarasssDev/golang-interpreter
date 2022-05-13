package main;

func f(out chan int, i int) int {
	out <- i + 1;
	return 0;
}

func g(in chan int, out chan int) int {
	var x int = <- in;
	out <- x * 2; 
	return 0;
}

func h(in chan int, out chan int) int {
	var x int = <- in;
	out <- x + 42; 
	return 0;
}


func main() {
	var ch1 chan int = make(chan int);
	var ch2 chan int = make(chan int);
	var ch3 chan int = make(chan int);

	var i int = 0;
	for ;i < 100; i = i + 1 {
		go g(ch1, ch2);
	}
	i = 0;

	for ;i < 100; i = i + 1 {
		go h(ch2, ch3);
	}
	i = 0;

	for ;i < 100; i = i + 1 {
		go f(ch1, i);
	}
	i = 0;

	for ;i < 100; i = i + 1 {
		println( <- ch3);
	}



}