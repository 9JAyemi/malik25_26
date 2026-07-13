module simple_calculator_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [3:0] control,
    input logic [7:0] result
);

    // When control=0000, result is the low 8 bits of a+b.
    check_add_operation: assert property (
        @(posedge clk) (control == 4'b0000) |-> (result == (a + b)[7:0])
    );

    // When control=0001, result is the low 8 bits of a-b.
    check_sub_operation: assert property (
        @(posedge clk) (control == 4'b0001) |-> (result == (a - b)[7:0])
    );

    // When control=0010, result is the low 8 bits of a*b.
    check_mul_operation: assert property (
        @(posedge clk) (control == 4'b0010) |-> (result == (a * b)[7:0])
    );

    // When control=0011 and b!=0, result equals a/b.
    check_div_operation_nonzero: assert property (
        @(posedge clk) (control == 4'b0011 && (b != 8'h00)) |-> (result == (a / b))
    );

    // For any other control value, result is zero.
    check_default_zero: assert property (
        @(posedge clk) (!(control inside {4'b0000,4'b0001,4'b0010,4'b0011})) |-> (result == 8'h00)
    );

    // For multiply with a==0, result must be zero.
    check_mul_zero_a: assert property (
        @(posedge clk) (control == 4'b0010 && (a == 8'h00)) |-> (result == 8'h00)
    );

    // For multiply with b==0, result must be zero.
    check_mul_zero_b: assert property (
        @(posedge clk) (control == 4'b0010 && (b == 8'h00)) |-> (result == 8'h00)
    );

    // For add with b==0, result equals a.
    check_add_identity_b: assert property (
        @(posedge clk) (control == 4'b0000 && (b == 8'h00)) |-> (result == a)
    );

    // For subtract with b==0, result equals a.
    check_sub_identity_b: assert property (
        @(posedge clk) (control == 4'b0001 && (b == 8'h00)) |-> (result == a)
    );

    // For divide with b==1, result equals a.
    check_div_by_one: assert property (
        @(posedge clk) (control == 4'b0011 && (b == 8'h01)) |-> (result == a)
    );

endmodule