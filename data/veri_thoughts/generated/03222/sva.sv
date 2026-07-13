module max_selector_assertions (
    input logic clk,
    input logic [4:0] a,
    input logic [4:0] b,
    input logic [4:0] c,
    input logic [1:0] out
);

    // A is selected when it was at least as large as B and C.
    check_a_selected_when_a_is_max: assert property (
        @(posedge clk) disable iff ($initstate)
        (($past(a) >= $past(b)) && ($past(a) >= $past(c))) |-> (out == 2'b00)
    );

    // B is selected when it beat A and was at least as large as C.
    check_b_selected_when_b_is_priority_max: assert property (
        @(posedge clk) disable iff ($initstate)
        (($past(b) > $past(a)) && ($past(b) >= $past(c))) |-> (out == 2'b01)
    );

    // C is selected when it was strictly larger than A and B.
    check_c_selected_when_c_is_strict_max: assert property (
        @(posedge clk) disable iff ($initstate)
        (($past(c) > $past(a)) && ($past(c) > $past(b))) |-> (out == 2'b10)
    );

    // Output code 00 means A was the selected maximum.
    check_out_00_implies_a_was_max: assert property (
        @(posedge clk) disable iff ($initstate)
        (out == 2'b00) |-> (($past(a) >= $past(b)) && ($past(a) >= $past(c)))
    );

    // Output code 01 means B beat A and was at least C.
    check_out_01_implies_b_was_priority_max: assert property (
        @(posedge clk) disable iff ($initstate)
        (out == 2'b01) |-> (($past(b) > $past(a)) && ($past(b) >= $past(c)))
    );

    // Output code 10 means C was the strict maximum.
    check_out_10_implies_c_was_strict_max: assert property (
        @(posedge clk) disable iff ($initstate)
        (out == 2'b10) |-> (($past(c) > $past(a)) && ($past(c) > $past(b)))
    );

    // The RTL never assigns the unreachable 2'b11 code.
    check_out_never_11: assert property (
        @(posedge clk) disable iff ($initstate)
        (out != 2'b11)
    );

endmodule