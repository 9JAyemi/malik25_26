module top_module (
    input clk,
    input reset,
    input [1:0] d,
    output [4:0] q
);

reg [2:0] shift_reg_async;
reg [1:0] shift_reg_sync;

// Asynchronous reset for the 3-bit shift register
always @(posedge clk, negedge reset) begin
    if (!reset) begin
        shift_reg_async <= 3'b0;
    end else begin
        shift_reg_async <= {shift_reg_async[1:0], d};
    end
end

// Synchronous reset for the 2-bit shift register
always @(posedge clk) begin
    if (reset) begin
        shift_reg_sync <= 2'b0;
    end else begin
        shift_reg_sync <= {shift_reg_sync[0], d[1]};
    end
end

// Functional module that combines the two shift registers
assign q = {shift_reg_async, shift_reg_sync};

endmodule

// Inputs and outputs for the two given modules
module shift_register_async (
    input clk,
    input reset,
    input d,
    output reg [2:0] q
);

// Asynchronous reset for the 3-bit shift register
always @(posedge clk, negedge reset) begin
    if (!reset) begin
        q <= 3'b0;
    end else begin
        q <= {q[1:0], d};
    end
end

endmodule

module shift_register_sync (
    input clk,
    input reset,
    input [1:0] d,
    output reg [1:0] q
);

// Synchronous reset for the 2-bit shift register
always @(posedge clk) begin
    if (reset) begin
        q <= 2'b0;
    end else begin
        q <= {q[0], d[1]};
    end
end

endmodule