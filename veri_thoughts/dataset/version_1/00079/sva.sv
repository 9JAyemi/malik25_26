module mux_4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic [3:0] out
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // out must route in0 when sel is 2'b00.
    check_sel_00_routes_in0: assert property (
        @($global_clock) (sel == 2'b00) |-> (out == in0)
    );

    // out must route in1 when sel is 2'b01.
    check_sel_01_routes_in1: assert property (
        @($global_clock) (sel == 2'b01) |-> (out == in1)
    );

    // out must route in2 when sel is 2'b10.
    check_sel_10_routes_in2: assert property (
        @($global_clock) (sel == 2'b10) |-> (out == in2)
    );

    // out must route in3 when sel is 2'b11.
    check_sel_11_routes_in3: assert property (
        @($global_clock) (sel == 2'b11) |-> (out == in3)
    );

    // If sel and the selected input stay stable, out must stay stable.
    check_selected_path_stability: assert property (
        @($global_clock)
        (! $initstate &&
         $stable(sel) &&
         (((sel == 2'b00) && $stable(in0)) ||
          ((sel == 2'b01) && $stable(in1)) ||
          ((sel == 2'b10) && $stable(in2)) ||
          ((sel == 2'b11) && $stable(in3))))
        |-> $stable(out)
    );

endmodule