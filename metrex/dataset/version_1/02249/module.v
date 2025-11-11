module top_module (
    input clk,         // Clock input
    input reset,       // Synchronous active-high reset
    input [7:0] in,    // 8-bit input signal for the edge detector
    input select,      // Select input to choose between counter and edge detector
    output [3:0] counter_out,  // 4-bit output from the counter
    output [7:0] edge_out,     // 8-bit output from the edge detector
    output [7:0] and_out       // Output from the functional module
);

    // Counter module
    reg [3:0] counter_reg;
    always @(posedge clk) begin
        if (reset) begin
            counter_reg <= 4'b0;
        end else begin
            counter_reg <= counter_reg + 1;
        end
    end
    assign counter_out = counter_reg;

    // Edge detector module
    reg [7:0] edge_reg;
    reg [7:0] edge_out_reg;
    always @(posedge clk) begin
        edge_reg <= {edge_reg[6:0], in};
        if (edge_reg[7] != edge_reg[6]) begin
            edge_out_reg <= 8'b11111111;
        end else begin
            edge_out_reg <= edge_out_reg;
        end
    end
    assign edge_out = edge_out_reg;

    // Functional module
    reg [7:0] and_out_reg;
    always @(posedge clk) begin
        if (select) begin
            and_out_reg <= edge_out_reg & counter_reg;
        end else begin
            and_out_reg <= 8'b0;
        end
    end
    assign and_out = and_out_reg;

endmodule