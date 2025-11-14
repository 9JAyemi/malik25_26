// SVA for round_counter_module
// Bind this module to the DUT to check/cover key behavior concisely.

module round_counter_module_sva (
  input logic        clk, reset, pulse, clk_1,
  input logic        work,
  input logic [11:0] mileage, number_of_halfkm,
  input logic [7:0]  ib,
  input logic [11:0] sample,
  input logic        flag,
  input logic [11:0] count
);

  // Reset behavior (clk domain)
  assert property (@(posedge clk) !reset |-> (ib==0 && mileage==0 && sample==0 && number_of_halfkm==0));

  // Sample/flag behavior (clk domain)
  assert property (@(posedge clk) disable iff(!reset) (pulse==0) |=> sample == $past(sample)+1);
  assert property (@(posedge clk) disable iff(!reset) (pulse==1) |=> (sample==0 && flag==1));

  // Event behavior when sample threshold reached (clk domain)
  // ib>=1 branch: mileage increments; halfkm increments when mileage%5==4
  assert property (@(posedge clk) disable iff(!reset)
                   (pulse==0 && flag==1 && sample>=49 && ib>=1)
                   |=> (flag==0 && ib==0
                        && mileage == $past(mileage)+1
                        && number_of_halfkm == $past(number_of_halfkm) + (($past(mileage)%5==4)?1:0)));

  // ib<1 branch: only ib increments; others hold
  assert property (@(posedge clk) disable iff(!reset)
                   (pulse==0 && flag==1 && sample>=49 && ib<1)
                   |=> (flag==0 && ib == $past(ib)+1
                        && mileage == $past(mileage)
                        && number_of_halfkm == $past(number_of_halfkm)));

  // ib only changes on the event; ib confined to {0,1}
  assert property (@(posedge clk) disable iff(!reset)
                   (ib != $past(ib)) |-> (pulse==0 && flag==1 && sample>=49));
  assert property (@(posedge clk) disable iff(!reset) (ib inside {[0:1]}));

  // Mileage monotonic; only changes on ib>=1 event and by +1
  assert property (@(posedge clk) disable iff(!reset) mileage >= $past(mileage));
  assert property (@(posedge clk) disable iff(!reset)
                   (mileage != $past(mileage))
                   |-> (pulse==0 && flag==1 && sample>=49 && ib>=1 && mileage==$past(mileage)+1));

  // number_of_halfkm monotonic; only increments when mileage%5==4 on ib>=1 event
  assert property (@(posedge clk) disable iff(!reset) number_of_halfkm >= $past(number_of_halfkm));
  assert property (@(posedge clk) disable iff(!reset)
                   (number_of_halfkm != $past(number_of_halfkm))
                   |-> (pulse==0 && flag==1 && sample>=49 && ib>=1 && ($past(mileage)%5==4)
                        && number_of_halfkm==$past(number_of_halfkm)+1));

  // Work/count behavior (clk_1 domain, async controlled by flag)
  // While flag==0, work=1 and count=0
  assert property (@(posedge clk_1) (flag==0) |-> (work==1 && count==0));

  // While flag==1 and count<4, count increments and work holds
  assert property (@(posedge clk_1) (flag==1 && count<4)
                   |=> (count==$past(count)+1 && work==$past(work)));

  // When flag==1 and count>=4, work goes low and count holds
  assert property (@(posedge clk_1) (flag==1 && count>=4)
                   |=> (work==0 && count==$past(count)));

  // After flag rises, work must deassert by 5 clk_1 cycles
  assert property (@(posedge clk_1) $rose(flag) |-> ##5 work==0);

  // Simple X-checks on reset-driven regs (clk domain)
  assert property (@(posedge clk) !reset |-> !$isunknown({ib,mileage,sample,number_of_halfkm}));

  // Coverage
  cover property (@(posedge clk) disable iff(!reset)
                  (pulse==0 && flag==1 && sample>=49 && ib<1));
  cover property (@(posedge clk) disable iff(!reset)
                  (pulse==0 && flag==1 && sample>=49 && ib>=1));
  cover property (@(posedge clk) disable iff(!reset)
                  (pulse==0 && flag==1 && sample>=49 && ib>=1 && ($past(mileage)%5==4)));
  cover property (@(posedge clk_1) $rose(flag) ##5 work==0);

endmodule

// Bind into the DUT (connects to internal regs)
bind round_counter_module round_counter_module_sva
  (.clk(clk), .reset(reset), .pulse(pulse), .clk_1(clk_1),
   .work(work), .mileage(mileage), .number_of_halfkm(number_of_halfkm),
   .ib(ib), .sample(sample), .flag(flag), .count(count));