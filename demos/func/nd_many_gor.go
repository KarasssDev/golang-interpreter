package main;

func f(ch chan int, res chan int) int {
	var x int = <- ch;
	println(x);
	res <- x - 1;
	return 0;
}


func main() {
	var ch chan int = make(chan int);
	var res chan int = make(chan int);
	var i int = 0;
	var cnt int = 1000;
	for ;i < cnt; i = i + 1 {
		go f(ch, res);
	}
	i = 0;
	for ;i < cnt; i = i + 1 {
		ch <- i * 10;
	}
	i = 0;
	for ;i < cnt; i = i + 1 {
		println( <- res );
	}
}