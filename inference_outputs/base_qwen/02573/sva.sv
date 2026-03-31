```systemverilog
module ripple_carry_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] OUT
);

    // Combinational logic: SUM and COUT are determined by A, B, and CIN
    // CIN is not present in the inputs, so it is assumed to be 0
    // The SUM and COUT are calculated in the full_adder module
    // The OUT is assigned the SUM from the full_adder module

    // Property to check if SUM is calculated correctly
    property p_sum;
        @(posedge clk) disable iff (!reset_n) OUT == (A + B);
    endproperty
    assert property (p_sum) else $error("SUM calculation is incorrect");

    // Property to check if COUT is calculated correctly
    property p_cout;
        @(posedge clk) disable iff (!reset_n) (OUT[3] == (A[3] + B[3]));
    endproperty
    assert property (p_cout) else $error("COUT calculation is incorrect");

endmodule
```