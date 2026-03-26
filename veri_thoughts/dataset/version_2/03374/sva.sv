module mux_encoder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic [1:0] SEL,
    input logic [3:0] Q
);

    function automatic logic [3:0] highest_priority_value(
        input logic [3:0] a,
        input logic [3:0] b,
        input logic [3:0] c,
        input logic [3:0] d
    );
    begin
        if ((d >= c) && (d >= b) && (d >= a))
            highest_priority_value = d;
        else if ((c >= b) && (c >= a))
            highest_priority_value = c;
        else if (b >= a)
            highest_priority_value = b;
        else
            highest_priority_value = a;
    end
    endfunction

    // Q is the selected A input ORed with the greatest input value.
    check_sel_00_q_value: assert property (
        @($global_clock) (SEL == 2'b00) |-> (Q == (highest_priority_value(A, B, C, D) | A))
    );

    // Q is the selected B input ORed with the greatest input value.
    check_sel_01_q_value: assert property (
        @($global_clock) (SEL == 2'b01) |-> (Q == (highest_priority_value(A, B, C, D) | B))
    );

    // Q is the selected C input ORed with the greatest input value.
    check_sel_10_q_value: assert property (
        @($global_clock) (SEL == 2'b10) |-> (Q == (highest_priority_value(A, B, C, D) | C))
    );

    // Q is the selected D input ORed with the greatest input value.
    check_sel_11_q_value: assert property (
        @($global_clock) (SEL == 2'b11) |-> (Q == (highest_priority_value(A, B, C, D) | D))
    );

    // Selecting A returns A when A is greater than or equal to every input.
    check_sel_00_a_is_greatest: assert property (
        @($global_clock) ((SEL == 2'b00) && (A >= B) && (A >= C) && (A >= D)) |-> (Q == A)
    );

    // Selecting B returns B when B is greater than or equal to every input.
    check_sel_01_b_is_greatest: assert property (
        @($global_clock) ((SEL == 2'b01) && (B >= A) && (B >= C) && (B >= D)) |-> (Q == B)
    );

    // Selecting C returns C when C is greater than or equal to every input.
    check_sel_10_c_is_greatest: assert property (
        @($global_clock) ((SEL == 2'b10) && (C >= A) && (C >= B) && (C >= D)) |-> (Q == C)
    );

    // Selecting D returns D when D is greater than or equal to every input.
    check_sel_11_d_is_greatest: assert property (
        @($global_clock) ((SEL == 2'b11) && (D >= A) && (D >= B) && (D >= C)) |-> (Q == D)
    );

endmodule