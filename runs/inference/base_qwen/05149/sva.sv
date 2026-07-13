module comparator_sva(
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic EQ,
    input logic GT
);
    // A > B
    property p_a_greater_b;
        @(posedge clk) disable iff (!rst_n) A > B;
    endproperty
    a_greater_b: assert property (p_a_greater_b) else $error("A is not greater than B");

    // C > D
    property p_c_greater_d;
        @(posedge clk) disable iff (!rst_n) C > D;
    endproperty
    c_greater_d: assert property (p_c_greater_d) else $error("C is not greater than D");

    // EQ is true if A == B == C == D
    property p_eq;
        @(posedge clk) disable iff (!rst_n) (A == B) && (B == C) && (C == D) |-> EQ;
    endproperty
    eq: assert property (p_eq) else $error("EQ is not true when A == B == C == D");

    // GT is true if A > B or (A == B and C > D)
    property p_gt;
        @(posedge clk) disable iff (!rst_n) (A > B) || ((A == B) && (C > D)) |-> GT;
    endproperty
    gt: assert property (p_gt) else $error("GT is not true when A > B or (A == B and C > D)");

    // EQ is false if A != B or B != C or C != D
    property p_not_eq;
        @(posedge clk) disable iff (!rst_n) !((A == B) && (B == C) && (C == D)) |-> !EQ;
    endproperty
    not_eq: assert property (p_not_eq) else $error("EQ is true when A != B or B != C or C != D");

    // GT is false if A <= B and (A != B or C <= D)
    property p_not_gt;
        @(posedge clk) disable iff (!rst_n) !(A > B) && ((A != B) || (C <= D)) |-> !GT;
    endproperty
    not_gt: assert property (p_not_gt) else $error("GT is true when A <= B and (A != B or C <= D)");

    // EQ is true if A == B and C == D
    property p_eq_c_d;
        @(posedge clk) disable iff (!rst_n) (A == B) && (C == D) |-> EQ;
    endproperty
    eq_c_d: assert property (p_eq_c_d) else $error("EQ is not true when A == B and C == D");

    // GT is true if A > B and C > D
    property p_gt_a_b_c_d;
        @(posedge clk) disable iff (!rst_n) (A > B) && (C > D) |-> GT;
    endproperty
    gt_a_b_c_d: assert property (p_gt_a_b_c_d) else $error("GT is not true when A > B and C > D");

    // EQ is false if A != B and C != D
    property p_not_eq_c_d;
        @(posedge clk) disable iff (!rst_n) !(A == B) && !(C == D) |-> !EQ;
    endproperty
    not_eq_c_d: assert property (p_not_eq_c_d) else $error("EQ is true when A != B and C != D");

    // GT is false if A <= B and C <= D
    property p_not_gt_a_b_c_d;
        @(posedge clk) disable iff (!rst_n) !(A > B) && !(C > D) |-> !GT;
    endproperty
    not_gt_a_b_c_d: assert property (p_not_gt_a_b_c_d) else $error("GT is true when A <= B and C <= D");
endmodule