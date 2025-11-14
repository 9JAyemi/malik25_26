// SVA checkers and binds for the design

// Ripple-carry adder functional checker
module rc_adder_sva #(parameter W=16)
(
    input  logic [W-1:0] a,
    input  logic [W-1:0] b,
    input  logic         carry_in,
    input  logic [W-1:0] sum,
    input  logic         carry_out
);
    logic [W:0] expected;
    assign expected = {1'b0,a} + {1'b0,b} + carry_in;

    // Functional equivalence (sum and carry)
    assert property (@(a or b or carry_in or sum or carry_out)
        {carry_out, sum} == expected);

    // No X on outputs when inputs are known
    assert property (@(a or b or carry_in or sum or carry_out)
        !$isunknown({a,b,carry_in}) |-> !$isunknown({sum,carry_out}));

    // Useful coverage
    cover property (@(a or b or carry_in) expected[W] == 1'b1);     // overflow
    cover property (@(a or b or carry_in) expected == '0);          // zero result
endmodule

bind ripple_carry_adder rc_adder_sva #(.W(16)) rc_adder_chk (
    .a(a), .b(b), .carry_in(carry_in), .sum(sum), .carry_out(carry_out)
);


// Top-level functional checker (muxing and overall function)
module top_module_sva
(
    input  logic [15:0] a,
    input  logic [15:0] b,
    input  logic        sub,
    input  logic        control,
    input  logic [15:0] out,
    input  logic        carry_out
);
    logic [16:0] add_exp;
    logic [15:0] xor_exp;
    assign add_exp = {1'b0,a} + {1'b0,b} + sub;
    assign xor_exp = b ^ {16{sub}};

    // Top-level output function
    assert property (@(a or b or sub or control or out)
        out == (control ? add_exp[15:0] : xor_exp));

    // Adder carry observed at top level
    assert property (@(a or b or sub or carry_out)
        carry_out == add_exp[16]);

    // No X on out when inputs are known
    assert property (@(a or b or sub or control or out)
        !$isunknown({a,b,sub,control}) |-> !$isunknown(out));

    // Coverage: exercise both branches and key cases
    cover property (@(a or b or sub or control)  control && (add_exp[16] == 1'b1)); // add overflow
    cover property (@(a or b or sub or control)  !control && !sub && (out == b));   // XOR pass-through
    cover property (@(a or b or sub or control)  !control &&  sub && (out == ~b));  // XOR invert
    cover property (@(a or b or sub or control)  control);                          // add branch hit
    cover property (@(a or b or sub or control) !control);                          // xor branch hit
endmodule

bind top_module top_module_sva top_chk (
    .a(a), .b(b), .sub(sub), .control(control), .out(out), .carry_out(carry_out)
);