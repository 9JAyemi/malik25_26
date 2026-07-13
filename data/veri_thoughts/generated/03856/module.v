
module mux_ff(
    input clk,
    input [3:0] in,
    input [1:0] sel,
    output reg q
);

    reg selected_signal;

    // Register initialization
    initial begin
        q <= 0;
    end

    always @(*) begin
        case (sel)
            2'b00: selected_signal = in[0];
            2'b01: selected_signal = in[1];
            2'b10: selected_signal = in[2];
            2'b11: selected_signal = in[3];
        endcase
    end

    always @(posedge clk) begin
        q <= selected_signal;
    end

endmodule