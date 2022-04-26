package main;

func main() {

	var i int = 0;

	for ;i < 3; i = i + 1 {
		println(i);
	}
	i = 0;

	for ;i < 3; {
		i = i + 1;
		println(i);
	}
	i = 0;

	for ;; {
		println(i);
		break;
	}

	for ;i < 20; {
		i = i + 1;

		if i == 7 {
			println(42);
			continue;
		} else {
			println(i);
		}

		if i == 7 || i == 10 {
			break;
		}

	}
}