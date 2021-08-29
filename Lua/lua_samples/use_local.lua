x = 10

function xChanger(value)
    local x = value
    print(x)
end 

xChanger(5)

print(x)

-- ### Result ### 
-- 5 (xChanger's local x value)
-- 10 (global scope's x value)