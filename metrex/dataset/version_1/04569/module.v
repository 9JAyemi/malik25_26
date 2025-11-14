module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [2:0] sel, // Select inputs for the multiplexer
    input [3:0] data, // Data inputs for the multiplexer
    output q, // Output from the flip-flop
    output [3:0] mux_out, // Output from the multiplexer
    output final_output // Output from the additive functional module
);

    // 3-input, 4-output multiplexer
    mux3to4 mux_inst (
        .sel(sel),
        .data_in(data),
        .data_out(mux_out)
    );

    // Dual-edge triggered flip-flop
    reg [1:0] count;
    always @(posedge clk, negedge reset) begin
        if (reset == 0) begin
            count <= 2'b00;
        end else begin
            count <= count + 1;
        end
    end
    assign q = count[1];

    // Additive functional module
    assign final_output = (count >= mux_out) ? 1'b1 : 1'b0;

endmodule

// 3-input, 4-output multiplexer
module mux3to4 (
    input [2:0] sel,
    input [3:0] data_in,
    output reg [3:0] data_out
);
    always @(*) begin
        case (sel)
            3'b000: data_out = data_in[0];
            3'b001: data_out = data_in[1];
            3'b010: data_out = data_in[2];
            3'b011: data_out = data_in[3];
            3'b100: data_out = data_in[0];
            3'b101: data_out = data_in[1];
            3'b110: data_out = data_in[2];
            3'b111: data_out = data_in[3];
        endcase
    end
endmodule