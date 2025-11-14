// Bind this SVA module to the DUT:
// bind denise_collision denise_collision_sva sva();

module denise_collision_sva;
  // Clocking/disables
  default clocking cb @(posedge clk); endclocking
  default disable iff (!clk7_en);

  // Shorthand
  let wr_clxcon  = (reg_address_in[8:1] == CLXCON[8:1]);
  let wr_clxcon2 = (reg_address_in[8:1] == CLXCON2[8:1]);
  let rd_clxdat  = (reg_address_in[8:1] == CLXDAT[8:1]);

  // Golden combinational expectations
  wire [3:0] sprmatch_exp = {
    (nsprite[6] | (nsprite[7] & clxcon[15])),
    (nsprite[4] | (nsprite[5] & clxcon[14])),
    (nsprite[2] | (nsprite[3] & clxcon[13])),
    (nsprite[0] | (nsprite[1] & clxcon[12]))
  };

  wire [7:0] bm_exp = (bpldata[7:0] ^ ~{clxcon2[1:0],clxcon[5:0]})
                    | (~{clxcon2[7:6],clxcon[11:6]});

  wire [14:0] cl_exp = {
    (sprmatch[2] & sprmatch[3]),  //14
    (sprmatch[1] & sprmatch[3]),  //13
    (sprmatch[1] & sprmatch[2]),  //12
    (sprmatch[0] & sprmatch[3]),  //11
    (sprmatch[0] & sprmatch[2]),  //10
    (sprmatch[0] & sprmatch[1]),  //9
    (evenmatch & sprmatch[3]),    //8
    (evenmatch & sprmatch[2]),    //7
    (evenmatch & sprmatch[1]),    //6
    (evenmatch & sprmatch[0]),    //5
    (oddmatch  & sprmatch[3]),    //4
    (oddmatch  & sprmatch[2]),    //3
    (oddmatch  & sprmatch[1]),    //2
    (oddmatch  & sprmatch[0]),    //1
    (evenmatch & oddmatch)        //0
  };

  // Combinational equivalences
  assert property (sprmatch == sprmatch_exp);
  assert property (bm == bm_exp);
  assert property (evenmatch == (bm[7] & bm[5] & bm[3] & bm[1]));
  assert property (oddmatch  == (bm[6] & bm[4] & bm[2] & bm[0] & (dblpf | evenmatch)));
  assert property (cl == cl_exp);

  // clxcon behavior
  assert property (reset |-> ##0 clxcon == 16'h0fff);
  assert property (!reset && wr_clxcon  |-> ##0 clxcon == data_in);
  assert property (!reset && !wr_clxcon |-> ##0 clxcon == $past(clxcon));

  // clxcon2 behavior
  assert property (reset                       |-> ##0 clxcon2 == 16'h0000);
  assert property (!reset && wr_clxcon         |-> ##0 clxcon2 == 16'h0000);
  assert property (!reset && aga && wr_clxcon2 |-> ##0 clxcon2 == data_in);
  assert property (!reset && !aga && wr_clxcon2|-> ##0 clxcon2 == $past(clxcon2));
  assert property (!reset && !wr_clxcon && !(aga && wr_clxcon2) |-> ##0 clxcon2 == $past(clxcon2));

  // clxdat_read_del tracking
  assert property (1'b1 |-> ##0 clxdat_read_del == rd_clxdat);

  // clxdat clear on falling edge of read, else sticky OR of collisions
  assert property ($fell(rd_clxdat) |-> ##0 clxdat == 15'd0);
  assert property (!$fell(rd_clxdat) |-> ##0 clxdat == ($past(clxdat) | cl));

  // data_out mapping
  assert property ( rd_clxdat |-> data_out == {1'b1, clxdat});
  assert property (!rd_clxdat |-> data_out == 16'd0);

  // Coverage
  cover property (reset);
  cover property (wr_clxcon);
  cover property (aga && wr_clxcon2);
  cover property (!aga && wr_clxcon2);
  cover property ($rose(rd_clxdat));
  cover property ($fell(rd_clxdat) ##0 (clxdat == 15'd0));
  cover property (evenmatch && !oddmatch);
  cover property (oddmatch && !evenmatch);  // requires dblpf
  cover property (oddmatch && evenmatch);
  cover property (!oddmatch && !evenmatch);
  cover property (sprmatch[0]);
  cover property (sprmatch[1]);
  cover property (sprmatch[2]);
  cover property (sprmatch[3]);
  cover property ($fell(rd_clxdat) ##1 (cl != 15'd0) ##0 (clxdat != 15'd0));
endmodule