module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic out_final
);

// out_final equals (a^b) & (c^d).
    check_function_equivalence: assert property (
        @(posedge clk) out_final == ((a ^ b) & (c ^ d))
    );

// When a==b, out_final equals c^d.
    check_when_a_eq_b: assert property (
        @(posedge clk) (a == b) |-> (out_final == (c ^ d))
    );

// When c==d, out_final equals a^b.
    check_when_c_eq_d: assert property (
        @(posedge clk) (c == d) |-> (out_final == (a ^ b))
    );

// When a^b==0, out_final must be 0.
    check_when_ab_xor0: assert property (
        @(posedge clk) ((a ^ b) == 1'b0) |-> (out_final == 1'b0)
    );

// When c^d==0, out_final must be 0.
    check_when_cd_xor0: assert property (
        @(posedge clk) ((c ^ d) == 1'b0) |-> (out_final == 1'b0)
    );

// When a^b==1 and c^d==1, out_final must be 1.
    check_when_ab_cd_xor1: assert property (
        @(posedge clk) (((a ^ b) == 1'b1) && ((c ^ d) == 1'b1)) |-> (out_final == 1'b1)
    );

// When a^b==1 and c^d==0, out_final must be 0.
    check_when_ab_xor1_cd0: assert property (
        @(posedge clk) (((a ^ b) == 1'b1) && ((c ^ d) == 1'b0)) |-> (out_final == 1'b0)
    );

// When a^b==0 and c^d==1, out_final must be 0.
    check_when_ab0_cd_xor1: assert property (
        @(posedge clk) (((a ^ b) == 1'b0) && ((c ^ d) == 1'b1)) |-> (out_final == 1'b0)
    );

endmodule
