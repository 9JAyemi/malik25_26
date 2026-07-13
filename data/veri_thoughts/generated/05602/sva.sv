module DCSC_sva #(
    parameter DCSMODE = "POS"
) (
    input logic CLK1,
    input logic CLK0,
    input logic SEL1,
    input logic SEL0,
    input logic MODESEL,
    input logic DCSOUT
);

    wire DCS_OR;
    wire DCS_XOR;
    wire DCS_AND;

    assign DCS_OR  = CLK1 | CLK0;
    assign DCS_XOR = CLK1 ^ CLK0;
    assign DCS_AND = CLK1 & CLK0;

    // Sample on both clock inputs; the RTL has no reset and is combinational.
    generate
        if (DCSMODE == "NEG") begin : gen_neg

            // MODESEL forces the inverted AND path.
            check_neg_modesel_forces_inv_and: assert property (
                @(posedge CLK1 or negedge CLK1 or posedge CLK0 or negedge CLK0)
                MODESEL |-> (DCSOUT == ~DCS_AND)
            );

            // SEL1=1, SEL0=0 still drives inverted AND in NEG mode.
            check_neg_sel10_forces_inv_and: assert property (
                @(posedge CLK1 or negedge CLK1 or posedge CLK0 or negedge CLK0)
                (!MODESEL && SEL1 && !SEL0) |-> (DCSOUT == ~DCS_AND)
            );

            // SEL1=0, SEL0=1 drives inverted CLK0 in NEG mode.
            check_neg_sel01_forces_inv_clk0: assert property (
                @(posedge CLK1 or negedge CLK1 or posedge CLK0 or negedge CLK0)
                (!MODESEL && !SEL1 && SEL0) |-> (DCSOUT == ~CLK0)
            );

            // SEL1=1, SEL0=1 still drives inverted AND in NEG mode.
            check_neg_sel11_forces_inv_and: assert property (
                @(posedge CLK1 or negedge CLK1 or posedge CLK0 or negedge CLK0)
                (!MODESEL && SEL1 && SEL0) |-> (DCSOUT == ~DCS_AND)
            );

            // SEL1=0, SEL0=0 still drives inverted AND in NEG mode.
            check_neg_sel00_forces_inv_and: assert property (
                @(posedge CLK1 or negedge CLK1 or posedge CLK0 or negedge CLK0)
                (!MODESEL && !SEL1 && !SEL0) |-> (DCSOUT == ~DCS_AND)
            );

        end else begin : gen_pos

            // MODESEL forces the AND path.
            check_pos_modesel_forces_and: assert property (
                @(posedge CLK1 or negedge CLK1 or posedge CLK0 or negedge CLK0)
                MODESEL |-> (DCSOUT == DCS_AND)
            );

            // SEL1=1, SEL0=0 routes CLK1 to the output.
            check_pos_sel10_routes_clk1: assert property (
                @(posedge CLK1 or negedge CLK1 or posedge CLK0 or negedge CLK0)
                (!MODESEL && SEL1 && !SEL0) |-> (DCSOUT == CLK1)
            );

            // SEL1=0, SEL0=1 routes the AND path to the output.
            check_pos_sel01_routes_and: assert property (
                @(posedge CLK1 or negedge CLK1 or posedge CLK0 or negedge CLK0)
                (!MODESEL && !SEL1 && SEL0) |-> (DCSOUT == DCS_AND)
            );

            // SEL1=1, SEL0=1 routes the OR path to the output.
            check_pos_sel11_routes_or: assert property (
                @(posedge CLK1 or negedge CLK1 or posedge CLK0 or negedge CLK0)
                (!MODESEL && SEL1 && SEL0) |-> (DCSOUT == DCS_OR)
            );

            // SEL1=0, SEL0=0 routes the XOR path to the output.
            check_pos_sel00_routes_xor: assert property (
                @(posedge CLK1 or negedge CLK1 or posedge CLK0 or negedge CLK0)
                (!MODESEL && !SEL1 && !SEL0) |-> (DCSOUT == DCS_XOR)
            );

        end
    endgenerate

endmodule