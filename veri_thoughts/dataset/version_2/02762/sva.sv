module mux64_sva #(
    parameter MUX_SIZE = 64
) (
    input  logic                 clk,
    input  logic [MUX_SIZE-1:0]  datai,
    input  logic [5:0]           A,
    input  logic [5:0]           B,
    input  logic [5:0]           C,
    input  logic                 datao
);

    // When concatenation equals 0, datao must be datai[0].
    sel_0_routes_bit0: assert property (
        @(posedge clk) disable iff (1'b0) ({C,B,A} == 18'd0) |-> (datao == datai[0])
    );

    // When concatenation equals 32, datao must be datai[0].
    sel_32_routes_bit0: assert property (
        @(posedge clk) disable iff (1'b0) ({C,B,A} == 18'd32) |-> (datao == datai[0])
    );

    // When concatenation is neither 0 nor 32, datao must be datai[1].
    other_sel_routes_bit1: assert property (
        @(posedge clk) disable iff (1'b0) !(({C,B,A} == 18'd0) || ({C,B,A} == 18'd32)) |-> (datao == datai[1])
    );

    // Explicit check for 31 case label: datao must be datai[1].
    sel_31_routes_bit1: assert property (
        @(posedge clk) disable iff (1'b0) ({C,B,A} == 18'd31) |-> (datao == datai[1])
    );

    // Output must always equal either datai[0] or datai[1].
    output_from_bit0_or_bit1_only: assert property (
        @(posedge clk) disable iff (1'b0) 1'b1 |-> ((datao == datai[0]) || (datao == datai[1]))
    );

    // If datai[0] equals datai[1], datao equals that value regardless of select.
    equal_inputs_pass_through: assert property (
        @(posedge clk) disable iff (1'b0) (datai[0] === datai[1]) |-> (datao == datai[0])
    );

    // If selection stays in {0,32} across cycles and datai[0] is stable, datao is stable.
    stable_when_in_bit0_region: assert property (
        @(posedge clk) disable iff (1'b0)
            $past((({C,B,A} == 18'd0) || ({C,B,A} == 18'd32))) &&
            (({C,B,A} == 18'd0) || ({C,B,A} == 18'd32)) &&
            ($past(datai[0]) == datai[0]) |-> (datao == $past(datao))
    );

    // If selection stays outside {0,32} across cycles and datai[1] is stable, datao is stable.
    stable_when_in_bit1_region: assert property (
        @(posedge clk) disable iff (1'b0)
            !$past((({C,B,A} == 18'd0) || ({C,B,A} == 18'd32))) &&
            !((({C,B,A} == 18'd0) || ({C,B,A} == 18'd32))) &&
            ($past(datai[1]) == datai[1]) |-> (datao == $past(datao))
    );

    // If inputs differ and datao equals datai[0], select must be 0 or 32.
    di0_implies_bit0_region_when_inputs_differ: assert property (
        @(posedge clk) disable iff (1'b0)
            ((datai[0] != datai[1]) && (datao == datai[0])) |-> (({C,B,A} == 18'd0) || ({C,B,A} == 18'd32))
    );

    // If inputs differ and select is not {0,32}, datao must be datai[1].
    non_bit0_region_implies_di1_when_inputs_differ: assert property (
        @(posedge clk) disable iff (1'b0)
            ((datai[0] != datai[1]) && !((({C,B,A} == 18'd0) || ({C,B,A} == 18'd32)))) |-> (datao == datai[1])
    );

endmodule