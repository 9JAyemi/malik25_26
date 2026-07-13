
module top_module ( 
    input wire [2:0] vec,
    input wire select,
    output wire [2:0] outv,
    output reg o2,
    output reg o1,
    output reg o0  );
    
    wire [2:0] mux_out;
    wire [7:0] decoder_out;
    
    // Multiplexers
    assign mux_out[0] = select ? vec[0] : 1'b0;
    assign mux_out[1] = select ? vec[1] : 1'b0;
    assign mux_out[2] = select ? vec[2] : 1'b0;
    
    // Decoders
    assign decoder_out[0] = ~(|vec);
    assign decoder_out[1] = (vec[1:0] == 2'b00) | (vec[1:0] == 2'b11);
    assign decoder_out[2] = vec[2];
    assign decoder_out[3] = (vec[1:0] == 2'b01) | (vec[1:0] == 2'b10);
    assign decoder_out[4] = vec[2] & (~vec[1]);
    assign decoder_out[5] = vec[0] & (~vec[2]);
    assign decoder_out[6] = vec[1] & (~vec[2]);
    assign decoder_out[7] = vec[1] & vec[0] & vec[2];
    
    // Output assignments
    assign outv = mux_out;
    always @(*) begin
        o2 = decoder_out[2];
        o1 = decoder_out[1];
        o0 = decoder_out[0];
    end
    
endmodule