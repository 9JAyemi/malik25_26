module simple_calculator_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic       OP,
    input logic       CLK,
    input logic       RST,
    input logic [7:0] C
);

// Reset clears the output on the next clock.
    check_reset_clears_c: assert property (
        @(posedge CLK) RST |=> (C == 8'h00)
    );

// When OP is 1, C captures A - B on the next clock.
    check_subtract_result: assert property (
        @(posedge CLK) disable iff (RST)
        (OP == 1'b1) |=> (C == ($past(A) - $past(B)))
    );

// When OP is 0, C captures A + B on the next clock.
    check_add_result: assert property (
        @(posedge CLK) disable iff (RST)
        (OP == 1'b0) |=> (C == ($past(A) + $past(B)))
    );

// With B==0, subtract behaves like a bitwise NOT.
    check_subtract_zero_rhs: assert property (
        @(posedge CLK) disable iff (RST)
        (OP == 1'b1 && B == 8'h00) |=> (C == ~$past(A))
    );

// With B==0, add returns A unchanged.
    check_add_zero_rhs: assert property (
        @(posedge CLK) disable iff (RST)
        (OP == 1'b0 && B == 8'h00) |=> (C == $past(A))
    );

// With A==0, subtract returns B unchanged.
    check_subtract_zero_lhs: assert property (
        @(posedge CLK) disable iff (RST)
        (OP == 1'b1 && A == 8'h00) |=> (C == $past(B))
    );

// With A==0, add behaves like a bitwise NOT.
    check_add_zero_lhs: assert property (
        @(posedge CLK) disable iff (RST)
        (OP == 1'b0 && A == 8'h00) |=> (C == ~$past(B))
    );

endmodule
