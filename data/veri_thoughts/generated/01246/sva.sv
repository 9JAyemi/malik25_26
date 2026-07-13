module mux4_sva #(
    parameter int WIDTH = 32,
    parameter int DISABLED = 0
)(
    input  logic                   clk,       // sampling clock for SVA
    input  logic                   reset_n,   // active-low reset for SVA
    input  logic                   en,
    input  logic [1:0]             sel,
    input  logic [WIDTH-1:0]       i0,
    input  logic [WIDTH-1:0]       i1,
    input  logic [WIDTH-1:0]       i2,
    input  logic [WIDTH-1:0]       i3,
    input  logic [WIDTH-1:0]       o
);
    // Cast DISABLED to WIDTH bits for comparisons
    localparam bit [WIDTH-1:0] DISABLED_VAL = bit [WIDTH-1:0]'(DISABLED);

    ///// Mux behavior /////
    // When en is LOW, output drives DISABLED value.
    check_output_when_disabled: assert property (
        @(posedge clk) disable iff (!reset_n) (!en) |-> (o == DISABLED_VAL)
    );

    // When en is HIGH and sel==2'b00, output equals i0.
    check_sel00_to_i0: assert property (
        @(posedge clk) disable iff (!reset_n) (en && (sel == 2'b00)) |-> (o == i0)
    );

    // When en is HIGH and sel==2'b01, output equals i1.
    check_sel01_to_i1: assert property (
        @(posedge clk) disable iff (!reset_n) (en && (sel == 2'b01)) |-> (o == i1)
    );

    // When en is HIGH and sel==2'b10, output equals i2.
    check_sel10_to_i2: assert property (
        @(posedge clk) disable iff (!reset_n) (en && (sel == 2'b10)) |-> (o == i2)
    );

    // When en is HIGH and sel==2'b11, output equals i3.
    check_sel11_to_i3: assert property (
        @(posedge clk) disable iff (!reset_n) (en && (sel == 2'b11)) |-> (o == i3)
    );

    // Structural: lower half mux selected when sel[1]==0.
    check_lower_half_mux: assert property (
        @(posedge clk) disable iff (!reset_n) (en && (sel[1] == 1'b0)) |-> (o == (sel[0] ? i1 : i0))
    );

    // Structural: upper half mux selected when sel[1]==1.
    check_upper_half_mux: assert property (
        @(posedge clk) disable iff (!reset_n) (en && (sel[1] == 1'b1)) |-> (o == (sel[0] ? i3 : i2))
    );

    // Full functional equivalence to ternary expression.
    check_full_expr_equivalence: assert property (
        @(posedge clk) disable iff (!reset_n)
            1'b1 |-> (o == (en ? (sel[1] ? (sel[0] ? i3 : i2) : (sel[0] ? i1 : i0)) : DISABLED_VAL))
    );

    // Stability: if en and sel==00 and i0 stable, output remains stable.
    check_stable_sel00: assert property (
        @(posedge clk) disable iff (!reset_n) (en && (sel == 2'b00) && $stable(i0) && $stable(en) && $stable(sel)) |-> $stable(o)
    );

    // Stability: if en and sel==11 and i3 stable, output remains stable.
    check_stable_sel11: assert property (
        @(posedge clk) disable iff (!reset_n) (en && (sel == 2'b11) && $stable(i3) && $stable(en) && $stable(sel)) |-> $stable(o)
    );
endmodule