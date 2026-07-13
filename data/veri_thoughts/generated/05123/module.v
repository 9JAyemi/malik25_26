module my_module (
    input clk,
    input din,
    input reset_n,
    input stdsync,
    output dout
);

    wire [0:0] wire_dffpipe3_q;

    dffpipe_l2c dffpipe3 (
        .clock(clk),
        .clrn(reset_n),
        .d(din),
        .q(wire_dffpipe3_q)
    );

    assign dout = wire_dffpipe3_q;

endmodule

module dffpipe_l2c (
    input clock,
    input clrn,
    input d,
    output reg [0:0] q
);

    always @(posedge clock or negedge clrn) begin
        if (~clrn) begin
            q <= 1'b0;
        end else begin
            q <= d;
        end
    end

endmodule