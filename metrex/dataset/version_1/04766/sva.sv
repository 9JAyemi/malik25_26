// Bind this module to regfile for assertions and coverage
bind regfile regfile_sva u_regfile_sva();

module regfile_sva;

  // Default clocking and reset masking for non-reset checks
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  function automatic logic [15:0] sext8 (input logic [7:0] v);
    return {{8{v[7]}}, v};
  endfunction

  // Reset values (sync reset)
  assert property (@(posedge clk)
    rst |=> r[0]==16'd0  && r[1]==16'd0  && r[2]==16'd0  && r[3]==16'd0  &&
                 r[4]==16'd0  && r[5]==16'd0  && r[6]==16'd0  && r[7]==16'd0  &&
                 r[8]==16'd0  && r[9]==16'hf000 &&
                 r[10]==16'd0 && r[11]==16'd0 && r[12]==16'd0 && r[13]==16'd0 &&
                 r[14]==16'd0 && r[15]==16'hfff0 &&
                 flags==9'd0);

  // Combinational mappings
  assert property (cs == r[9]);
  assert property (ip == r[15]);
  assert property (s  == r[{2'b10, addr_s}]);

  // Read port A
  assert property ((a_byte && ~addr_a[3]) |-> a == sext8(a8));
  assert property ((!a_byte || addr_a[3]) |-> a == r[addr_a]);
  assert property ( addr_a[2] |-> a8 == r[addr_a[1:0]][15:8]);
  assert property (!addr_a[2] |-> a8 == r[addr_a][7:0]);

  // Read port B
  assert property ((b_byte && ~addr_b[3]) |-> b == sext8(b8));
  assert property ((!b_byte || addr_b[3]) |-> b == r[addr_b]);
  assert property ( addr_b[2] |-> b8 == r[addr_b[1:0]][15:8]);
  assert property (!addr_b[2] |-> b8 == r[addr_b][7:0]);

  // Read port C
  assert property ((c_byte && ~addr_c[3]) |-> c == sext8(c8));
  assert property ((!c_byte || addr_c[3]) |-> c == r[addr_c]);
  assert property ( addr_c[2] |-> c8 == r[addr_c[1:0]][15:8]);
  assert property (!addr_c[2] |-> c8 == r[addr_c][7:0]);

  // cx_zero behavior
  assert property (cx_zero == ((addr_d==4'd1) ? (d==16'd0) : (r[1]==16'd0)));

`ifdef DEBUG
  // Debug taps
  assert property (ax == r[0]);
  assert property (dx == r[2]);
  assert property (bp == r[5]);
  assert property (si == r[6]);
  assert property (es == r[8]);
`endif

  // Flags write and stability
  assert property (wrfl |=> flags == $past(iflags));
  assert property (!wrfl |-> $stable(flags));

  // Highest-priority writes (must override any wr to same idx in same cycle)
  assert property (wrhi  |=> r[4'd2]  == $past(d[31:16]));
  assert property (wr_ip0 |=> r[4'd14] == $past(ip));

  // Word write
  assert property (wr && word_op &&
                   !(wrhi && (addr_d==4'd2)) &&
                   !(wr_ip0 && (addr_d==4'd14))
                   |=> r[addr_d] == $past(d[15:0]));

  // Byte op to segment class (addr_d[3:2]==2'b10) forces full-word sign-extend
  assert property (wr && !word_op && (addr_d[3:2]==2'b10) &&
                   !(wrhi && (addr_d==4'd2)) &&
                   !(wr_ip0 && (addr_d==4'd14))
                   |=> r[addr_d] == sext8($past(d[7:0])));

  // Low-byte write path
  assert property (wr && !word_op && (addr_d[3] ~^ addr_d[2]) &&
                   !(wrhi && (addr_d==4'd2)) &&
                   !(wr_ip0 && (addr_d==4'd14))
                   |=> r[addr_d] == { $past(r[addr_d][15:8]), $past(d[7:0]) });

  // High-byte write path (AL/AH family via {2'b00,addr_d[1:0]})
  assert property (wr && !word_op && !(addr_d[3:2]==2'b10) && !(addr_d[3] ~^ addr_d[2]) &&
                   !(wrhi && ({2'b00,addr_d[1:0]}==4'd2))
                   |=> r[{2'b00,addr_d[1:0]}] ==
                       { $past(d[7:0]), $past(r[{2'b00,addr_d[1:0]}][7:0]) });

  // Functional coverage
  cover property (rst ##1 !rst);
  cover property (wr && word_op);
  cover property (wr && !word_op && (addr_d[3:2]==2'b10));
  cover property (wr && !word_op && (addr_d[3] ~^ addr_d[2]));
  cover property (wr && !word_op && !(addr_d[3:2]==2'b10) && !(addr_d[3] ~^ addr_d[2]));
  cover property (wr && wrhi  && (addr_d==4'd2));
  cover property (wr && wr_ip0 && (addr_d==4'd14));
  cover property (wrfl);
  cover property (a_byte && ~addr_a[3] &&  addr_a[2]==1'b0);
  cover property (a_byte && ~addr_a[3] &&  addr_a[2]==1'b1);
  cover property (b_byte && ~addr_b[3] &&  addr_b[2]==1'b0);
  cover property (b_byte && ~addr_b[3] &&  addr_b[2]==1'b1);
  cover property (c_byte && ~addr_c[3] &&  addr_c[2]==1'b0);
  cover property (c_byte && ~addr_c[3] &&  addr_c[2]==1'b1);
  cover property (a_byte && ~addr_a[3] && a8[7]); // negative sign-extend case
  cover property ((addr_d==4'd1) && (d==16'd0)  &&  cx_zero);
  cover property ((addr_d!=4'd1) && (r[1]==16'd0) && cx_zero);
  cover property ((addr_d==4'd1) && (d!=16'd0)  && !cx_zero);
  cover property ((addr_d!=4'd1) && (r[1]!=16'd0) && !cx_zero);

endmodule