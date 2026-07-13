
module data_modifier(
    input [31:0] reg_input,
    input [3:0] address,
    input reg_out_syn,
    input ack,
    input ack_syn,
    output reg [31:0] reg_out
);

reg [31:0] shifted_input;
reg [31:0] reversed_input;
reg [31:0] reg_out_nxt;

always @(*) begin
    if (ack && !ack_syn) begin
        shifted_input = {reg_input[30:0], 1'b0};
        reg_out_nxt     = shifted_input;
    end
    else if (!ack && ack_syn) begin
        shifted_input = {1'b0, reg_input[31:1]};
        reg_out_nxt     = shifted_input;
    end
    else if (ack && ack_syn) begin
        reversed_input = {reg_input[7:0], reg_input[15:8], reg_input[23:16], reg_input[31:24]};
        reg_out_nxt     = reversed_input;
    end
    else begin
        reg_out_nxt = reg_input;
    end
end

wire reg_out_syn_nxt;
assign reg_out_syn_nxt = ack || ack_syn;

reg reg_out_syn_nxt_r;
always @(*) begin
    reg_out_syn_nxt_r = reg_out_syn_nxt;
end

reg reg_out_syn_r;
always @(*) begin
    reg_out_syn_r <= reg_out_syn_nxt_r;
end

assign reg_out_syn = reg_out_syn_r;

always @(*) begin
    reg_out = reg_out_nxt;
end

endmodule