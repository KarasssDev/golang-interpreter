package main;

func main(){
	var t bool = true;
	var f bool = false;

	println(!t);
	println(!f);

	println(t && t);
	println(t && f);
	println(f && t);
	println(f && f);

	println(t || t);
	println(t || f);
	println(f || t);
	println(f || f);

	println( (t || f) && f);
	println( t || f && f);
	println( (t || f) && !f);
}