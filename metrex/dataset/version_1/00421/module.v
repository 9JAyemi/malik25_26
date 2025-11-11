module accu(
    input               clk         ,   
    input               rst_n       ,
    input       [7:0]   data_in     ,
    input               valid_a     ,
    input               ready_b     ,
 
    output              ready_a     ,
    output  reg         valid_b     ,
    output  reg [7:0]   data_out
);

    // Pipeline registers for adder and multiplier outputs
    reg [7:0] adder_out_reg;
    reg [7:0] mult_out_reg;
    
    // Counter to keep track of input data
    reg [2:0] count = 0;
    
    // Instantiate adder and multiplier modules
    adder_module adder_inst(.a(adder_out_reg), .b(data_in), .sum(adder_out_reg));
    multiplier_module mult_inst(.a(mult_out_reg), .b(data_in), .product(mult_out_reg));
    
    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            valid_b <= 0;
            data_out <= 0;
            count <= 0;
        end
        else begin
            // Check if downstream module is ready
            if (ready_b && valid_a) begin
                // Increment counter
                count <= count + 1;
                
                // Accumulate data every 6 input data
                if (count == 6) begin
                    // Calculate final output using adder and multiplier outputs
                    data_out <= (adder_out_reg + mult_out_reg) / 2;
                    valid_b <= 1;
                    count <= 0;
                end
                else begin
                    valid_b <= 0;
                end
            end
        end
    end
    
    // Handshake signals
    assign ready_a = ~valid_b;
    
endmodule

module adder_module (
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum
);
    assign sum = a + b;
endmodule

module multiplier_module (
    input [7:0] a,
    input [7:0] b,
    output [7:0] product
);
    assign product = a * b;
endmodule