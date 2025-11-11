module dc_offset_removal 
  #(parameter WIDTH=16,
    parameter ADDR=8'd0,
    parameter alpha_shift=20)
   (input clk, input rst, 
    input set_stb, input [7:0] set_addr, input [31:0] set_data,
    input [WIDTH-1:0] in, output [WIDTH-1:0] out);
   
   wire 	      set_now = set_stb & (ADDR == set_addr);
   
   reg 		      fixed;  // uses fixed offset
   wire [WIDTH-1:0]   fixed_dco;

   localparam int_width = WIDTH + alpha_shift;
   reg [int_width-1:0] integrator;
   wire [WIDTH-1:0]    quantized;

   always @(posedge clk)
     if(rst)
       begin
	  fixed <= 0;
	  integrator <= {int_width{1'b0}};
       end
     else if(set_now)
       begin
	  fixed <= set_data[31];
	  if(set_data[30])
	    integrator <= {set_data[29:0],{(int_width-30){1'b0}}};
       end
     else if(~fixed)
       integrator <= integrator +  {{(alpha_shift){in[WIDTH-1]}},in};

   round_sd #(.WIDTH_IN(int_width),.WIDTH_OUT(WIDTH)) round_sd
     (.clk(clk), .reset(rst), .in(integrator), .strobe_in(1'b1), .out(quantized), .strobe_out());
   
   add2_and_clip_reg #(.WIDTH(WIDTH)) add2_and_clip_reg
     (.clk(clk), .rst(rst), .in1(in), .in2(-quantized), .strobe_in(1'b1), .sum(out), .strobe_out());

endmodule

// Round to nearest with saturation
module round_sd #(parameter WIDTH_IN=16, WIDTH_OUT=16) (
    input clk,
    input reset,
    input signed [WIDTH_IN-1:0] in,
    input strobe_in,
    output reg signed [WIDTH_OUT-1:0] out,
    output reg strobe_out
);
    localparam WIDTH_OUT_1 = WIDTH_OUT - 1;
    localparam WIDTH_IN_1 = WIDTH_IN - 1;
    localparam WIDTH_DIFF = WIDTH_IN - WIDTH_OUT;
    localparam WIDTH_DIFF_1 = WIDTH_DIFF - 1;
    localparam ROUND_CONST = (1 << (WIDTH_DIFF - 1)) - 1;
    reg signed [WIDTH_IN_1:0] in_shifted;
    reg signed [WIDTH_OUT_1:0] out_shifted;
    reg [WIDTH_DIFF_1:0] round_bits;
    
    always @(posedge clk) begin
        if (reset) begin
            out <= 0;
            strobe_out <= 0;
            in_shifted <= 0;
            out_shifted <= 0;
            round_bits <= 0;
        end
        else if (strobe_in) begin
            in_shifted <= in >> WIDTH_DIFF;
            out_shifted <= in_shifted + round_bits;
            if (out_shifted > (1 << WIDTH_OUT_1) - 1) begin
                out <= (1 << WIDTH_OUT_1) - 1;
            end
            else if (out_shifted < -(1 << WIDTH_OUT_1)) begin
                out <= -(1 << WIDTH_OUT_1);
            end
            else begin
                out <= out_shifted;
            end
            round_bits <= ROUND_CONST & in[WIDTH_DIFF_1:0];
            strobe_out <= 1;
        end
        else begin
            strobe_out <= 0;
        end
    end
endmodule

// Add two signed numbers and clip the result to the range of [-2^(WIDTH-1), 2^(WIDTH-1)-1]
module add2_and_clip_reg #(parameter WIDTH=16) (
    input clk,
    input rst,
    input signed [WIDTH-1:0] in1,
    input signed [WIDTH-1:0] in2,
    input strobe_in,
    output reg signed [WIDTH-1:0] sum,
    output reg strobe_out
);
    always @(posedge clk) begin
        if (rst) begin
            sum <= 0;
            strobe_out <= 0;
        end
        else if (strobe_in) begin
            sum <= in1 + in2;
            if (sum > (1 << (WIDTH-1)) - 1) begin
                sum <= (1 << (WIDTH-1)) - 1;
            end
            else if (sum < -(1 << (WIDTH-1))) begin
                sum <= -(1 << (WIDTH-1));
            end
            strobe_out <= 1;
        end
        else begin
            strobe_out <= 0;
        end
    end
endmodule