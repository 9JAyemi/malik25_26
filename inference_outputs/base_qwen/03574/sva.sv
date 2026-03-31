```systemverilog
module square_module_sva (
    input logic [3:0] num,
    output logic [7:0] square
);
    // Combinational logic, so use @(posedge clk)
    // Check that the square of num is correctly calculated
    check_square: assert property (
        @(posedge clk) square == num * num
    ) else $error("Square calculation is incorrect");
endmodule
```