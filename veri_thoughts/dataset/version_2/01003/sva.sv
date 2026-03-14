module fifo_sva (
    input  logic        clk,
    input  logic        wr0a,
    input  logic        wr0b,
    input  logic        wr1a,
    input  logic        wr1b,
    input  logic [15:0] inData,
    input  logic [15:0] out0,
    input  logic [15:0] out1
);

    // wr0b causes out0 to take ~inData on the next cycle (B overrides A).
    property p_update_out0_on_wr0b;
        logic [15:0] din;
        @(posedge clk) (wr0b, din = inData) |=> (out0 == ~din);
    endproperty
    update_out0_on_wr0b: assert property (p_update_out0_on_wr0b);

    // wr0a without wr0b causes out0 to take inData on the next cycle.
    property p_update_out0_on_wr0a_only;
        logic [15:0] din;
        @(posedge clk) ((wr0a && !wr0b), din = inData) |=> (out0 == din);
    endproperty
    update_out0_on_wr0a_only: assert property (p_update_out0_on_wr0a_only);

    // If no write to mem[0], out0 holds its value on the next cycle.
    property p_hold_out0_when_no_write;
        logic [15:0] o;
        @(posedge clk) ((!wr0a && !wr0b), o = out0) |=> (out0 == o);
    endproperty
    hold_out0_when_no_write: assert property (p_hold_out0_when_no_write);

    // wr1b causes out1 to take ~inData on the next cycle (B overrides A).
    property p_update_out1_on_wr1b;
        logic [15:0] din;
        @(posedge clk) (wr1b, din = inData) |=> (out1 == ~din);
    endproperty
    update_out1_on_wr1b: assert property (p_update_out1_on_wr1b);

    // wr1a without wr1b causes out1 to take inData on the next cycle.
    property p_update_out1_on_wr1a_only;
        logic [15:0] din;
        @(posedge clk) ((wr1a && !wr1b), din = inData) |=> (out1 == din);
    endproperty
    update_out1_on_wr1a_only: assert property (p_update_out1_on_wr1a_only);

    // If no write to mem[1], out1 holds its value on the next cycle.
    property p_hold_out1_when_no_write;
        logic [15:0] o;
        @(posedge clk) ((!wr1a && !wr1b), o = out1) |=> (out1 == o);
    endproperty
    hold_out1_when_no_write: assert property (p_hold_out1_when_no_write);

    // When both wr0a and wr0b are asserted, out0 takes ~inData (B priority).
    property p_out0_priority_b_over_a;
        logic [15:0] din;
        @(posedge clk) ((wr0a && wr0b), din = inData) |=> (out0 == ~din);
    endproperty
    out0_priority_b_over_a: assert property (p_out0_priority_b_over_a);

    // When both wr1a and wr1b are asserted, out1 takes ~inData (B priority).
    property p_out1_priority_b_over_a;
        logic [15:0] din;
        @(posedge clk) ((wr1a && wr1b), din = inData) |=> (out1 == ~din);
    endproperty
    out1_priority_b_over_a: assert property (p_out1_priority_b_over_a);

    // Simultaneous wr0a-only and wr1a-only cause both out0/out1 to take inData.
    property p_both_a_only_updates_both_to_inData;
        logic [15:0] din;
        @(posedge clk) ((wr0a && !wr0b && wr1a && !wr1b), din = inData) |=> ((out0 == din) && (out1 == din));
    endproperty
    both_a_only_updates_both_to_inData: assert property (p_both_a_only_updates_both_to_inData);

    // Simultaneous wr0b and wr1b cause both out0/out1 to take ~inData.
    property p_both_b_updates_both_to_not_inData;
        logic [15:0] din;
        @(posedge clk) ((wr0b && wr1b), din = inData) |=> ((out0 == ~din) && (out1 == ~din));
    endproperty
    both_b_updates_both_to_not_inData: assert property (p_both_b_updates_both_to_not_inData);

    // Mixed: wr0b with wr1a-only updates out0 to ~inData and out1 to inData.
    property p_mixed_wr0b_wr1a_only;
        logic [15:0] din;
        @(posedge clk) ((wr0b && wr1a && !wr1b), din = inData) |=> ((out0 == ~din) && (out1 == din));
    endproperty
    mixed_wr0b_wr1a_only: assert property (p_mixed_wr0b_wr1a_only);

    // Mixed: wr0a-only with wr1b updates out0 to inData and out1 to ~inData.
    property p_mixed_wr0a_only_wr1b;
        logic [15:0] din;
        @(posedge clk) ((wr0a && !wr0b && wr1b), din = inData) |=> ((out0 == din) && (out1 == ~din));
    endproperty
    mixed_wr0a_only_wr1b: assert property (p_mixed_wr0a_only_wr1b);

endmodule