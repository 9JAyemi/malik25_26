
module clock_inverter(
    input wire clk,
    output reg Y
);

    // Inputs are registered
    reg Y_internal = ~clk;
    
    always @(posedge clk) begin
        Y <= Y_internal;
    end

endmodule