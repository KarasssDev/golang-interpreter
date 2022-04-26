package main;

func main() {
	if (0 < 1) {
		println(1);
	}

	if 0 > 1 {
		println(1);
	} else {
		println(2);
	}

	if 0 > 1 {
		println(1);
	} else if 0 < 1{
		println(2);
	} else {
		println(3);
	}

	if 0 > 1 {
		println(1);
	} else if 0 > 1{
		println(2);
	} else {
		println(3);
	}
}