module adder_4bit_sva (
    input logic       Cin,
    input logic       A,
    input logic       B,
    input logic       Clk,
    input logic       En,
    input logic       Rst,
    input logic [3:0] Sum,
    input logic       Cout
);

    // Synchronous reset clears both registered outputs.
    check_reset_clears_outputs: assert property (
        @(posedge Clk) Rst |=> ({Cout, Sum} == 5'b00000)
    );

    // With enable low, the registered outputs hold their value.
    check_hold_when_disabled: assert property (
        @(posedge Clk) disable iff (Rst)
        !En |=> $stable({Cout, Sum})
    );

    // With enable high, the next state is the previous sum plus Cin, A, and B.
    check_enable_updates_outputs: assert property (
        @(posedge Clk) disable iff (Rst)
        En |=> ({Cout, Sum} == ({1'b0, $past(Sum)} + $past(Cin) + $past(A) + $past(B)))
    );

    // With enable high and zero addends, the state does not change.
    check_zero_addends_hold_state: assert property (
        @(posedge Clk) disable iff (Rst)
        (En && !Cin && !A && !B) |=> $stable({Cout, Sum})
    );

    // With enable high and all three addends high, the state increments by three.
    check_all_addends_high_increment_by_three: assert property (
        @(posedge Clk) disable iff (Rst)
        (En && Cin && A && B) |=> ({Cout, Sum} == ({1'b0, $past(Sum)} + 5'd3))
    );

endmodule