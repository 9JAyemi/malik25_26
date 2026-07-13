module pipelined_mux_sva (
    input logic [2:0] sel,
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [3:0] data4,
    input logic [3:0] data5,
    input logic [3:0] out
);

    // sel 0 routes data0 to out.
    check_sel0_routes_data0: assert property (
        @($global_clock) (sel === 3'd0) |-> (out === data0)
    );

    // sel 1 routes data1 to out.
    check_sel1_routes_data1: assert property (
        @($global_clock) (sel === 3'd1) |-> (out === data1)
    );

    // sel 2 routes data2 to out.
    check_sel2_routes_data2: assert property (
        @($global_clock) (sel === 3'd2) |-> (out === data2)
    );

    // sel 3 routes data3 to out.
    check_sel3_routes_data3: assert property (
        @($global_clock) (sel === 3'd3) |-> (out === data3)
    );

    // sel 4 routes data4 to out.
    check_sel4_routes_data4: assert property (
        @($global_clock) (sel === 3'd4) |-> (out === data4)
    );

    // sel 5 routes data5 to out.
    check_sel5_routes_data5: assert property (
        @($global_clock) (sel === 3'd5) |-> (out === data5)
    );

    // Any unmapped sel value drives zero.
    check_default_routes_zero: assert property (
        @($global_clock)
        (!((sel === 3'd0) || (sel === 3'd1) || (sel === 3'd2) ||
           (sel === 3'd3) || (sel === 3'd4) || (sel === 3'd5)))
        |-> (out === 4'h0)
    );

    // Unselected inputs do not affect out when sel and the selected path are stable.
    check_unselected_inputs_do_not_affect_out: assert property (
        @($global_clock)
        ((((sel === 3'd0) && $stable(sel) && $stable(data0)) ||
          ((sel === 3'd1) && $stable(sel) && $stable(data1)) ||
          ((sel === 3'd2) && $stable(sel) && $stable(data2)) ||
          ((sel === 3'd3) && $stable(sel) && $stable(data3)) ||
          ((sel === 3'd4) && $stable(sel) && $stable(data4)) ||
          ((sel === 3'd5) && $stable(sel) && $stable(data5)) ||
          ((!((sel === 3'd0) || (sel === 3'd1) || (sel === 3'd2) ||
              (sel === 3'd3) || (sel === 3'd4) || (sel === 3'd5))) && $stable(sel))))
        |-> $stable(out)
    );

endmodule