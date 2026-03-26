
module usb_system_clocks_dffpipe_l2c(
    input clock,
    input clrn,
    input d,
    output q
);

    reg q_reg;

    always @(posedge clock or negedge clrn) begin
        if (~clrn) begin
            q_reg <= 1'b0;
        end else begin
            q_reg <= d;
        end
    end

    assign q = q_reg;

endmodule

module latch_module(
    input clk,
    input din,
    input reset_n,
    output dout
);

    reg dff_input;
    wire dff_output;

    always @ (posedge clk or negedge reset_n) begin
        if (~reset_n) begin
            dff_input <= 1'b0;
        end else begin
            dff_input <= din;
        end
    end

    assign dout = dff_output;

    usb_system_clocks_dffpipe_l2c dff_inst(
        .clock(clk),
        .clrn(reset_n),
        .d(dff_input),
        .q(dff_output)
    );

endmodule
