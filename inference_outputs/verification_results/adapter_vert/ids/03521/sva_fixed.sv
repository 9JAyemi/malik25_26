module mem_enc_dec_sva (
    input logic enc_data,
    input logic key,
    input logic mem_addr,
    input logic mem_data,
    input logic b0000000,
    input logic clk_gen_1
);

property MemLockeotid; @(posedge clk_gen_1) (mem_addr) |-> (enc_data) == (mem_data ^ key) ;endproperty
assert property (MemLockeotid);

property ValidDataeotid; @(posedge clk_gen_1) (mem_data) != (key) |-> (enc_data) != (mem_data) ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_gen_1) (mem_data) != (key) ||  (mem_addr) != 7'b0000000  |-> (enc_data) != (mem_data) ;endproperty
assert property (ValidDataeotid_2);

endmodule