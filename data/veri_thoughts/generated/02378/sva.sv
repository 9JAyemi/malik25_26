module mux_4to1_sva (
    input logic [3:0] data0,
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [3:0] data3,
    input logic [1:0] sel,
    input logic [3:0] result
);
    // Analysis: no clock/reset in RTL; pure combinational 4:1 mux; assertions clocked on $global_clock.

    // Result equals masked-OR of inputs per select.
    check_mux_masked_or_equivalence: assert property (
        @(posedge $global_clock)
        result == ( ({4{(sel == 2'b00)}} & data0)
                  | ({4{(sel == 2'b01)}} & data1)
                  | ({4{(sel == 2'b10)}} & data2)
                  | ({4{(sel == 2'b11)}} & data3) )
    );

    // When sel==00, result equals data0.
    check_sel00_routing: assert property (
        @(posedge $global_clock) (sel == 2'b00) |-> (result == data0)
    );

    // When sel==01, result equals data1.
    check_sel01_routing: assert property (
        @(posedge $global_clock) (sel == 2'b01) |-> (result == data1)
    );

    // When sel==10, result equals data2.
    check_sel10_routing: assert property (
        @(posedge $global_clock) (sel == 2'b10) |-> (result == data2)
    );

    // When sel==11, result equals data3.
    check_sel11_routing: assert property (
        @(posedge $global_clock) (sel == 2'b11) |-> (result == data3)
    );

    // If sel==00 and sel/data0 are stable, result remains stable.
    check_stable_sel00: assert property (
        @(posedge $global_clock) (sel == 2'b00) && $stable(sel) && $stable(data0) |-> $stable(result)
    );

    // If sel==01 and sel/data1 are stable, result remains stable.
    check_stable_sel01: assert property (
        @(posedge $global_clock) (sel == 2'b01) && $stable(sel) && $stable(data1) |-> $stable(result)
    );

    // If sel==10 and sel/data2 are stable, result remains stable.
    check_stable_sel10: assert property (
        @(posedge $global_clock) (sel == 2'b10) && $stable(sel) && $stable(data2) |-> $stable(result)
    );

    // If sel==11 and sel/data3 are stable, result remains stable.
    check_stable_sel11: assert property (
        @(posedge $global_clock) (sel == 2'b11) && $stable(sel) && $stable(data3) |-> $stable(result)
    );

    // If all inputs are equal, result equals that common value.
    check_all_inputs_equal_output: assert property (
        @(posedge $global_clock) ((data0 == data1) && (data1 == data2) && (data2 == data3)) |-> (result == data0)
    );

endmodule