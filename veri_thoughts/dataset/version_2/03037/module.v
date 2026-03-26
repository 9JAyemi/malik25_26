
module top_module (
    input clk,
    input reset,
    input [3:0] inputs, // 4-to-2 priority encoder inputs
    input up_down, // Up/Down input for the counter
    input load, // Load input for the counter
    input [3:0] D, // Input data for the counter
    output [3:0] Q // Output from the counter
);

wire [1:0] priority_encoder_output; // Output from the priority encoder

// Instantiate the 4-to-2 priority encoder module
priority_encoder priority_encoder_inst (
    .I(inputs),
    .O(priority_encoder_output)
);

// Instantiate the up/down counter module
up_down_counter up_down_counter_inst (
    .clk(clk),
    .reset(reset),
    .up_down(up_down),
    .load(load),
    .D(D), // Connect the input data to the input of the counter
    .Q(Q)
);

endmodule
module priority_encoder (
    input [3:0] I,
    output reg [1:0] O
);

    always @(*) begin
        case (I)
            4'b0001: O = 2'b01;
            4'b0010: O = 2'b10;
            4'b0100: O = 2'b11;
            default: O = 2'b00;
        endcase
    end

endmodule
module up_down_counter (
    input clk,
    input reset,
    input up_down,
    input load,
    input [3:0] D,
    output reg [3:0] Q
);

    always @(posedge clk) begin
        if (reset) begin
            Q <= 4'b0000;
        end else if (load) begin
            Q <= D;
        end else if (up_down) begin
            Q <= Q + 4'b0001;
        end else begin
            Q <= Q - 4'b0001;
        end
    end

endmodule