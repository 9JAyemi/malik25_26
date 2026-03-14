
module priority_encoder (
    input [3:0] in,
    output reg [1:0] pos,
    output reg       is_zero
);

    always @(*) begin
        if (|in == 1'b0) begin
            pos = 2'b00;
            is_zero = 1'b1;
        end else begin
            pos = {2{in[3]}};
            is_zero = 1'b0;
        end
    end

endmodule
module and_gate (
    input [3:0] in,
    input        is_zero,
    output       all_high
);

    assign all_high = (is_zero) ? 1'b0 : (in == 4'b1111);

endmodule
module top_module (
    input [3:0] in,
    output reg [1:0] pos,
    output       all_high
);

    wire [1:0] pos_wire;
    wire       is_zero;
    priority_encoder pe(.in(in), .pos(pos_wire), .is_zero(is_zero));
    and_gate ag(.in(in), .is_zero(is_zero), .all_high(all_high));

    always @(*) begin
        pos = pos_wire;
    end

endmodule