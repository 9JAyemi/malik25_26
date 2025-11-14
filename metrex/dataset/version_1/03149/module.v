
module shift_register (
    input [3:0] data_in,
    input shift_en,
    input load_en,
    output [3:0] data_out,
    output empty
);

reg [3:0] register;

assign empty = ~|register;
assign data_out = register;

always @(posedge shift_en) begin
  
    if (load_en ) begin
        register <= {data_in[2:0], 1'b0};
        
    end else if (shift_en ) begin
        register <= ( {register[2:0], 1'b0} ); 
    end
end
endmodule