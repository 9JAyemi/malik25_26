module twos_complement_sva (
    input logic clk,
    input logic [3:0] Y,
    input logic [3:0] A,
    input logic invert
);

// Y matches the RTL expression for all inputs.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ((invert) ? ~(~A + 4'b0001) : (~A + 4'b0001))
    );

// When invert is low, Y is the 4-bit sum of ~A and 1.
    check_sum_when_not_invert: assert property (
        @(posedge clk) !invert |-> (Y == (~A + 4'b0001))
    );

// When invert is high, Y is the bitwise complement of ~A.
    check_complement_when_invert: assert property (
        @(posedge clk) invert |-> (Y == ~(~A))
    );

// The least-significant bit follows the RTL expression.
    check_lsb_equation: assert property (
        @(posedge clk) Y[0] == ((invert) ? ~A[0] : (~A[0] ^ 1'b1))
    );

// With invert low, Y[1] is the RTL sum of ~A[1] and 1.
    check_bit1_sum_when_not_invert: assert property (
        @(posedge clk) (!invert && (A[0] == 1'b0)) |-> (Y[1] == (~A[1] ^ 1'b1))
    );

// With invert low, Y[1] is the RTL sum of ~A[1] and 0.
    check_bit1_sum_when_not_invert_carry: assert property (
        @(posedge clk) (!invert && (A[0] == 1'b1)) |-> (Y[1] == (~A[1]))
    );

// With invert high, Y[1] is the RTL complement of ~A[1].
    check_bit1_complement_when_invert: assert property (
        @(posedge clk) (invert && (A[0] == 1'b0)) |-> (Y[1] == ~A[1])
    );

// With invert high, Y[1] is the RTL complement of ~A[1] with carry.
    check_bit1_complement_when_invert_carry: assert property (
        @(posedge clk) (invert && (A[0] == 1'b1)) |-> (Y[1] == (~A[1] ^ 1'b1))
    );

// With invert low, Y[2] is the RTL sum of ~A[2] and 1.
    check_bit2_sum_when_not_invert: assert property (
        @(posedge clk) (!invert && (A[1:0] == 2'b00)) |-> (Y[2] == (~A[2] ^ 1'b1))
    );

// With invert low, Y[2] is the RTL sum of ~A[2] and 0.
    check_bit2_sum_when_not_invert_carry: assert property (
        @(posedge clk) (!invert && (A[1:0] == 2'b01)) |-> (Y[2] == (~A[2]))
    );

// With invert high, Y[2] is the RTL complement of ~A[2].
    check_bit2_complement_when_invert: assert property (
        @(posedge clk) (invert && (A[1:0] == 2'b00)) |-> (Y[2] == ~A[2])
    );

// With invert high, Y[2] is the RTL complement of ~A[2] with carry.
    check_bit2_complement_when_invert_carry: assert property (
        @(posedge clk) (invert && (A[1:0] == 2'b01)) |-> (Y[2] == (~A[2] ^ 1'b1))
    );

endmodule
