package main;

func producer(ch chan int) int {
	ch <- 41;
	return 0;
}

func consumer(ch chan int, res chan int) int {
	var x int = <- ch;
	res <- x + 1; 
	return 0;
}


func main() {
	var ch chan int = make(chan int);
	var res chan int = make(chan int);
	go consumer(ch, res);
	go producer(ch);
	println( <- res );
}