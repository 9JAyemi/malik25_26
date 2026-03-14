module top_module_sva (
    input logic CLK,

    input logic a,
    input logic b,
    input logic [1:0] sel2,
    input logic [3:0] data2_0,
    input logic [3:0] data2_1,
    input logic [1:0] sel1,
    input logic [3:0] data1_0,
    input logic [3:0] data1_1,
    input logic [3:0] data1_2,
    input logic [3:0] data1_3,
    input logic [3:0] data1_4,
    input logic [3:0] data1_5,
    input logic out_wire
);
    // out_wire implements XOR of a and b
    check_out_equals_xor: assert property (
        @(posedge CLK) out_wire == (a ^ b)
    );

    // If a and b are stable, out_wire remains stable
    check_out_stable_when_ab_stable: assert property (
        @(posedge CLK) ($stable(a) && $stable(b)) |-> $stable(out_wire)
    );

    // Toggling only a toggles out_wire
    check_out_changes_on_a_only_toggle: assert property (
        @(posedge CLK) ($changed(a) && $stable(b)) |-> $changed(out_wire)
    );

    // Toggling only b toggles out_wire
    check_out_changes_on_b_only_toggle: assert property (
        @(posedge CLK) ($changed(b) && $stable(a)) |-> $changed(out_wire)
    );

    // Toggling both a and b leaves out_wire stable (XOR invariance)
    check_out_stable_when_both_toggle: assert property (
        @(posedge CLK) ($changed(a) && $changed(b)) |-> $stable(out_wire)
    );

    // Any change on out_wire must be caused by a or b changing
    check_out_change_implies_ab_change: assert property (
        @(posedge CLK) $changed(out_wire) |-> ($changed(a) || $changed(b))
    );

    // Select inputs do not affect out_wire when a and b are stable
    check_out_independent_of_selects: assert property (
        @(posedge CLK) (($changed(sel1) || $changed(sel2)) && $stable(a) && $stable(b)) |-> $stable(out_wire)
    );

    // data1_* inputs do not affect out_wire when a and b are stable
    check_out_independent_of_data1: assert property (
        @(posedge CLK) (($changed(data1_0) || $changed(data1_1) || $changed(data1_2) || $changed(data1_3) || $changed(data1_4) || $changed(data1_5)) && $stable(a) && $stable(b)) |-> $stable(out_wire)
    );

    // data2_* inputs do not affect out_wire when a and b are stable
    check_out_independent_of_data2: assert property (
        @(posedge CLK) (($changed(data2_0) || $changed(data2_1)) && $stable(a) && $stable(b)) |-> $stable(out_wire)
    );

    // When a equals b, out_wire is 0 (XOR truth table)
    check_out_zero_when_equal: assert property (
        @(posedge CLK) (a == b) |-> (out_wire == 1'b0)
    );

    // When a differs from b, out_wire is 1 (XOR truth table)
    check_out_one_when_unequal: assert property (
        @(posedge CLK) (a != b) |-> (out_wire == 1'b1)
    );
endmodule