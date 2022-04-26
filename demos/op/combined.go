package main;

func main(){
	println( (3 + 3 == 6) || (4 < 7) || ("abc" == "ab" + "c") && (true == false) == true);
	println( (3 + 2 == 6) && (4 < 7) || ("abc" == "ab" + "c") && (true == false) != true);
	println( (3 + 3 == 6) && (4 > 7) || ("abcd" == "ab" + "c") && (true != false) == true);
	println( (3 + 4 == 6) || (4 < 7) || ("abce" != "ab" + "c") && (true == false) == true);
	println( (3 + 4 == 6) && (4 < 7) || ("abcf" == "ab" + "c") && (true == true)  == true);
}