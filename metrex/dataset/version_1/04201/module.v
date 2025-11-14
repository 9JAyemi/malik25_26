
module top_module (
    input clk,             // Clock input
    input reset,           // Synchronous active-high reset
    input [7:0] data_in,   // 8-bit input data
    input select,          // Select input to choose between accumulator modules
    output [9:0] data_out, // 10-bit output from the active accumulator module
    output ready_a,        // Output ready signal for upstream module
    input ready_b,         // Input ready signal from downstream module
    input valid_b          // Input valid signal from downstream module
);

// First accumulator module using counter-based architecture
reg [7:0] acc1;
reg [2:0] count1;
always @(posedge clk) begin
    if (reset) begin
        acc1 <= 0;
        count1 <= 0;
    end else begin
        if (count1 == 7) begin
            acc1 <= acc1 + data_in;
            count1 <= 0;
        end else begin
            count1 <= count1 + 1;
        end
    end
end

// Second accumulator module using pipeline structure
reg [7:0] acc2;
reg [7:0] sum;
reg [1:0] count2;
wire valid_a;        // Output valid signal for active accumulator module
always @(posedge clk) begin
    if (reset) begin
        acc2 <= 0;
        sum <= 0;
        count2 <= 0;
    end else begin
        if (count2 == 1) begin
            sum <= sum + data_in;
            acc2 <= acc2 + sum;
            sum <= 0;
            count2 <= 0;
        end else begin
            sum <= sum + data_in;
            count2 <= count2 + 1;
        end
    end
end

// Control logic to select active accumulator module
reg [1:0] select_reg;
always @(posedge clk) begin
    if (reset) begin
        select_reg <= 0;
    end else begin
        select_reg <= select;
    end
end

// Output data from active accumulator module
assign data_out = select_reg == 0 ? {acc1, 2'b00} : {acc2, 2'b00};
assign ready_a = ~select_reg ? valid_b : valid_b;
assign valid_a = select_reg == 0 ? count1 == 7 : count2 == 1;

endmodule