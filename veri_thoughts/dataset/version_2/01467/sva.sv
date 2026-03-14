module mux4_sva (
    input  logic clk,
    input  logic RESETn,
    input  logic enable,
    input  logic [1:0] select,
    input  logic in0,
    input  logic in1,
    input  logic in2,
    input  logic in3,
    input  logic out
);
    ///// Data selection when enabled /////
    // When enabled and select==0, out equals in0.
    map_enable_sel0: assert property (
        @(posedge clk) disable iff (!RESETn) (enable && (select == 2'b00)) |-> (out == in0)
    );
    // When enabled and select==1, out equals in1.
    map_enable_sel1: assert property (
        @(posedge clk) disable iff (!RESETn) (enable && (select == 2'b01)) |-> (out == in1)
    );
    // When enabled and select==2, out equals in2.
    map_enable_sel2: assert property (
        @(posedge clk) disable iff (!RESETn) (enable && (select == 2'b10)) |-> (out == in2)
    );
    // When enabled and select==3, out equals in3.
    map_enable_sel3: assert property (
        @(posedge clk) disable iff (!RESETn) (enable && (select == 2'b11)) |-> (out == in3)
    );

    ///// Output zero when disabled /////
    // When disabled and select==0, out is 0.
    map_disable_sel0: assert property (
        @(posedge clk) disable iff (!RESETn) (!enable && (select == 2'b00)) |-> (out == 1'b0)
    );
    // When disabled and select==1, out is 0.
    map_disable_sel1: assert property (
        @(posedge clk) disable iff (!RESETn) (!enable && (select == 2'b01)) |-> (out == 1'b0)
    );
    // When disabled and select==2, out is 0.
    map_disable_sel2: assert property (
        @(posedge clk) disable iff (!RESETn) (!enable && (select == 2'b10)) |-> (out == 1'b0)
    );
    // When disabled and select==3, out is 0.
    map_disable_sel3: assert property (
        @(posedge clk) disable iff (!RESETn) (!enable && (select == 2'b11)) |-> (out == 1'b0)
    );

    ///// Stability when enabled /////
    // If enabled, sel==0, and inputs/control stable, out is stable.
    stable_enabled_sel0: assert property (
        @(posedge clk) disable iff (!RESETn)
            (enable && (select == 2'b00) && $stable(enable) && $stable(select) && $stable(in0)) |-> $stable(out)
    );
    // If enabled, sel==1, and inputs/control stable, out is stable.
    stable_enabled_sel1: assert property (
        @(posedge clk) disable iff (!RESETn)
            (enable && (select == 2'b01) && $stable(enable) && $stable(select) && $stable(in1)) |-> $stable(out)
    );
    // If enabled, sel==2, and inputs/control stable, out is stable.
    stable_enabled_sel2: assert property (
        @(posedge clk) disable iff (!RESETn)
            (enable && (select == 2'b10) && $stable(enable) && $stable(select) && $stable(in2)) |-> $stable(out)
    );
    // If enabled, sel==3, and inputs/control stable, out is stable.
    stable_enabled_sel3: assert property (
        @(posedge clk) disable iff (!RESETn)
            (enable && (select == 2'b11) && $stable(enable) && $stable(select) && $stable(in3)) |-> $stable(out)
    );

    ///// Stability when disabled /////
    // If disabled, sel==0, and control stable, out is stable.
    stable_disabled_sel0: assert property (
        @(posedge clk) disable iff (!RESETn)
            (!enable && (select == 2'b00) && $stable(enable) && $stable(select)) |-> $stable(out)
    );
    // If disabled, sel==1, and control stable, out is stable.
    stable_disabled_sel1: assert property (
        @(posedge clk) disable iff (!RESETn)
            (!enable && (select == 2'b01) && $stable(enable) && $stable(select)) |-> $stable(out)
    );
    // If disabled, sel==2, and control stable, out is stable.
    stable_disabled_sel2: assert property (
        @(posedge clk) disable iff (!RESETn)
            (!enable && (select == 2'b10) && $stable(enable) && $stable(select)) |-> $stable(out)
    );
    // If disabled, sel==3, and control stable, out is stable.
    stable_disabled_sel3: assert property (
        @(posedge clk) disable iff (!RESETn)
            (!enable && (select == 2'b11) && $stable(enable) && $stable(select)) |-> $stable(out)
    );

endmodule