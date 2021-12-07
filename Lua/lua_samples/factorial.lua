function fact (n)
    if n == 0 then
        return 1
    else 
        return n * fact (n - 1)
    end
end


data = {1, 2, 3, 4, 5, 6, 7}
s = 0
for i = 1,7 do
    s = s + fact(data[i])
end
