```systemverilog
module ripple_carry_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    output logic [3:0] SUM
);

    // Combinational logic, but still use clocked assertions for consistency
    @(posedge clk) disable iff (!rst_n) begin
        // SUM is the result of the XOR of A, B, and CARRY_IN
        sum_check: assert property (
            (SUM == (A ^ B ^ CARRY_IN))
        ) else $error("SUM is not the correct result of A, B, and CARRY_IN");

        // CARRY_OUT is the result of (A & B) | (CARRY_IN & (A ^ B))
        carry_out_check: assert property (
            (CARRY_OUT == ((A & B) | (CARRY_IN & (A ^ B))))
        ) else $error("CARRY_OUT is not the correct result of A, B, and CARRY_IN");
    end

endmodule
```