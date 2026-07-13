
module counter_adder_module (
    input wire clk,
    input wire reset,
    input wire select,
    output wire [3:0] out
);

wire [3:0] counter;
wire [3:0] adder_out;

// Instantiate the counter module
counter_module counter_inst (
    .clk(clk),
    .reset(reset),
    .out(counter)
);

// Instantiate the adder module
adder_module adder_inst (
    .a(counter),
    .b(4'b0001),
    .out(adder_out)
);

// Control module to choose between counter and adder

reg [3:0] tmp_counter;  // Declare a temporary register to store the counter value
wire [3:0] selected_output;

always @(posedge clk) begin
    if (reset) begin
        tmp_counter <= 4'b0000;
    end else begin
        case (select)  
            1'b0: tmp_counter  <= counter;
            1'b1: tmp_counter  <= adder_out;
        endcase
    end
end

assign out = tmp_counter;  // Assign the output to the temporary register

endmodule
module counter_module (
    input wire clk,
    input wire reset,
    output wire [3:0] out
);

reg [3:0] counter_reg; // Declare counter as a reg

always @(posedge clk) begin
    if (reset) begin
        counter_reg <= 4'b0000;
    end else begin
        counter_reg <= counter_reg + 1;
    end
end

assign out = counter_reg; // Assign the output to the register value

endmodule
module adder_module (
    input wire [3:0] a,
    input wire [3:0] b,
    output wire [3:0] out
);

assign out = a + b; // Direct assignment for the adder output

endmodule