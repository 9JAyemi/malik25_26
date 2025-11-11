// SVA checker for execute_load_data
// Bind this module to the DUT and connect a sampling clk and rst_n.
module execute_load_data_sva (
  input logic              clk,
  input logic              rst_n,
  input logic [3:0]        iMASK,
  input logic [1:0]        iSHIFT,
  input logic [31:0]       iDATA,
  input logic [31:0]       oDATA
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional correctness
  ap_fullword:  assert property ( (iMASK == 4'hF)    |-> (oDATA == iDATA) );
  ap_byte_3:    assert property ( (iMASK == 4'b0001) |-> (oDATA == {24'h0, iDATA[31:24]}) );
  ap_byte_2:    assert property ( (iMASK == 4'b0010) |-> (oDATA == {24'h0, iDATA[23:16]}) );
  ap_byte_1:    assert property ( (iMASK == 4'b0100) |-> (oDATA == {24'h0, iDATA[15:8]})  );
  ap_byte_0:    assert property ( (iMASK == 4'b1000) |-> (oDATA == {24'h0, iDATA[7:0]})   );
  ap_hword_hi:  assert property ( (iMASK == 4'b0011) |-> (oDATA == {16'h0, iDATA[31:16]}) );
  ap_default:   assert property ( !(iMASK inside {4'hF,4'b0001,4'b0010,4'b0100,4'b1000,4'b0011})
                                   |-> (oDATA == {16'h0, iDATA[15:0]}) );

  // iSHIFT must not affect output
  ap_shift_indep: assert property ( $stable({iMASK,iDATA}) && !$stable(iSHIFT) |-> $stable(oDATA) );

  // X-propagation guard: known inputs imply known output
  ap_known: assert property ( !$isunknown({iMASK,iDATA}) |-> !$isunknown(oDATA) );

  // Functional coverage
  cp_fullword:  cover property (iMASK == 4'hF);
  cp_byte_3:    cover property (iMASK == 4'b0001);
  cp_byte_2:    cover property (iMASK == 4'b0010);
  cp_byte_1:    cover property (iMASK == 4'b0100);
  cp_byte_0:    cover property (iMASK == 4'b1000);
  cp_hword_hi:  cover property (iMASK == 4'b0011);
  cp_default:   cover property (!(iMASK inside {4'hF,4'b0001,4'b0010,4'b0100,4'b1000,4'b0011}));
  cp_shift_indep: cover property ($stable({iMASK,iDATA}) && !$stable(iSHIFT));

endmodule

// Example bind (edit clk/rst names to match your environment):
// bind execute_load_data execute_load_data_sva u_execute_load_data_sva(
//   .clk  (clk),
//   .rst_n(rst_n),
//   .iMASK(iMASK),
//   .iSHIFT(iSHIFT),
//   .iDATA(iDATA),
//   .oDATA(oDATA)
// );