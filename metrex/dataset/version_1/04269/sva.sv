// SVA for mem_encrypt_decrypt
// Bind this checker to the DUT
module sva_mem_encrypt_decrypt;
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic reset effects
  assert property (rst |=> (data_out==8'h00 && temp_data==8'h00));

  // Temp_data domain
  assert property (temp_data inside {8'h00,8'h01});

  // Address guard (always true for 8-bit, but assert anyway)
  assert property (address < 8'd256);

  // Write phase: when temp_data==0 and start, next cycle temp_data==1 and memory updated correctly
  assert property (
    start && (address<8'd256) && (temp_data==8'h00) |=> 
      (temp_data==8'h01) &&
      (mem[$past(address)] == ($past(key[0]) ? ~ $past(data_in) : ($past(data_in) ^ $past(key))))
  );

  // Read phase: when temp_data==1 and start, next cycle temp_data==0 and data_out updated correctly
  assert property (
    start && (address<8'd256) && (temp_data==8'h01) |=> 
      (temp_data==8'h00) &&
      (data_out == ($past(key[0]) ? ~ $past(mem[address]) : ($past(mem[address]) ^ $past(key))))
  );

  // No activity when start is low
  assert property (!start |=> $stable(temp_data) && $stable(data_out) && $stable(mem[$past(address)]));

  // data_out changes only due to read path
  assert property ($changed(data_out) |-> $past(start && (temp_data==8'h01) && (address<8'd256)));

  // mem write occurs only due to write path
  assert property (mem[$past(address)] != $past(mem[$past(address)]) |-> $past(start && (temp_data==8'h00) && (address<8'd256)));

  // End-to-end roundtrip: write then read same address with same key returns original data
  property roundtrip_same_addr;
    automatic logic [7:0] a, din, k;
    (start && temp_data==8'h00, a=address, din=data_in, k=key)
    ##1 (start && temp_data==8'h01 && address==a && key==k)
    |=> ##1 (data_out==din);
  endproperty
  assert property (roundtrip_same_addr);

  // Coverage
  cover property (start && temp_data==8'h00 && key[0]==1);
  cover property (start && temp_data==8'h00 && key[0]==0);
  cover property (start && temp_data==8'h01 && key[0]==1);
  cover property (start && temp_data==8'h01 && key[0]==0);
  cover property (roundtrip_same_addr);
endmodule

bind mem_encrypt_decrypt sva_mem_encrypt_decrypt sva();