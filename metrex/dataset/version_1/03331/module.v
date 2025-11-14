module flow_control_processing #(
    parameter SYMBOLS_PER_BEAT = 4,
    parameter BITS_PER_SYMBOL = 8
)(
    input clock,
    input reset,
    input internal_output_is_valid,
    input ena,
    input ready_out,
    output stall,
    output valid_out,
    output [SYMBOLS_PER_BEAT*BITS_PER_SYMBOL-1:0] data_out,
    output eop_out,
    output sop_out
);

reg [SYMBOLS_PER_BEAT*BITS_PER_SYMBOL-1:0] data_out_d1;
reg sop_out_d1, eop_out_d1;

assign stall = !ready_out;
assign valid_out = internal_output_is_valid & ena;

assign data_out = valid_out ? data_out_d1 : {(BITS_PER_SYMBOL * SYMBOLS_PER_BEAT){1'b0}};
assign eop_out = valid_out ? eop_out_d1 : 1'b0;
assign sop_out = valid_out ? sop_out_d1 : 1'b0;

always @(posedge clock or posedge reset)
    if (reset) begin
        data_out_d1 <= {(BITS_PER_SYMBOL * SYMBOLS_PER_BEAT){1'b0}};
        sop_out_d1 <= 1'b0;
        eop_out_d1 <= 1'b0;
    end
    else begin
        data_out_d1 <= data_out;
        sop_out_d1 <= sop_out;
        eop_out_d1 <= eop_out;
    end

endmodule