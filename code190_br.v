/**************************************************************************/
/* code190.v                          For CSC.T341 CLD Archlab TOKYO TECH */
/**************************************************************************/
`timescale 1ns/100ps
`default_nettype none //

/***** top module for simulation *****/
module m_top (); 
  reg r_clk=0; initial forever #50 r_clk = ~r_clk;
  wire [31:0] w_led;

//  initial $dumpfile("main.vcd");
//  initial $dumpvars(0, m_top);

  reg [31:0] r_cnt = 1;
  always@(posedge r_clk) r_cnt <= r_cnt + 1;
   
  m_proc14 p (r_clk, 1'b1, w_led);

  always@(posedge r_clk) $write("%7d %08x\n", r_cnt, p.Wb_rslt2);
//  initial begin
//     $write("clock: r_pc     IfId_pc  IdEx_pc  ExMe_pc  MeWb_pc : ");
//     $write("t Id_rrs1  Id_rrs2  Ex_ain   Ex_rslt  Wb_rslt2 w_led\n");
//  end
//  always@(posedge r_clk) 
//    $write("%5d: %08x %08x %08x %08x %08x: %d %08x %08x %08x %08x %08x %08x\n", 
//           r_cnt, p.r_pc, p.IfId_pc, p.IdEx_pc, p.ExMe_pc, p.MeWb_pc,  
//           p.Ex_taken, p.Id_rrs1, p.Id_rrs2, p.Ex_ain, p.Ex_rslt, p.Wb_rslt2, p.w_led);
  always@(posedge r_clk) if(w_led!=0) $finish;
  initial #50000000 $finish;
endmodule

/***** main module for FPGA implementation *****/
/*
module m_main (w_clk, w_led);
  input  wire w_clk;
  output wire [3:0] w_led;
 
  wire w_clk2, w_locked;
  clk_wiz_0 clk_w0 (w_clk2, 0, w_locked, w_clk);
   
  wire [31:0] w_dout;
  m_proc14 p (w_clk2, w_locked, w_dout);

  vio_0 vio_00(w_clk2, w_dout);
 
  reg [3:0] r_led = 0;
  always @(posedge w_clk2) 
    r_led <= {^w_dout[31:24], ^w_dout[23:16], ^w_dout[15:8], ^w_dout[7:0]};
  assign w_led = r_led;
endmodule
*/

/**************************************************************************/
module m_proc14 (w_clk, w_ce, w_led);
  input  wire w_clk, w_ce;
  output wire [31:0] w_led;

  reg [31:0] r_pc      = 0; // program counter
  reg [31:0] IfId_pc   = 0; // IfId pipeline registers
  reg [31:0] IfId_ir   = 0;

  reg [31:0] IdEx_pc   = 0; // IdEx pipeline registers
  reg [31:0] IdEx_ir   = 0;   
  reg [31:0] IdEx_tpc  = 0;
  reg [31:0] IdEx_rrs1 = 0;
  reg [31:0] IdEx_rrs2 = 0;   
  reg [31:0] IdEx_imm  = 0;
  reg [4:0]  IdEx_rd   = 0;

  reg [31:0] ExMe_pc   = 0; // ExMe pipeline registers
  reg [31:0] ExMe_ir   = 0;
  reg [31:0] ExMe_rslt = 0;
  reg [31:0] ExMe_rrs2 = 0;
  reg [4:0]  ExMe_rd   = 0;

  reg [31:0] MeWb_pc   = 0; // MeWb pipeline registers
  reg [31:0] MeWb_ir   = 0;
  reg [31:0] MeWb_rslt = 0;
  reg [31:0] MeWb_ldd  = 0;
  reg [4:0]  MeWb_rd   = 0;
  
  /*********************** IF stage *********************************/
  wire [31:0] If_ir;
  wire [11:0] pc_mux;
  assign pc_mux = w_vb ? w_addr : r_pc[13:2];
  m_amemory m_imem (w_clk, pc_mux, 1'd0, 32'd0, If_ir);

  always @(posedge w_clk) #5 if(w_ce) begin
      if (Ex_taken) begin
          IfId_pc <= 0;
      end else if (w_vb) begin
          IfId_pc <= {w_addr, 2'b00};
      end else begin
          IfId_pc <= IdEx_pc + 4;
      end
      IfId_ir <= (Ex_taken) ? {25'd0, 7'b0010011} : If_ir;
  end



  /*********************** ID stage *********************************/
  wire [4:0] Id_op5 = IfId_ir[6:2];
  wire [4:0] Id_rs1 = IfId_ir[19:15];
  wire [4:0] Id_rs2 = IfId_ir[24:20];
  wire [4:0] Id_rd  = IfId_ir[11:7];
  wire Id_we = (Id_op5==5'b01100 || Id_op5==5'b00100 || Id_op5==5'b00000);
  wire [31:0] Id_imm, Id_rrs1, Id_rrs2;
  m_immgen m_immgen0 (IfId_ir, Id_imm);
  m_rf_bypass m_regs (w_clk, Id_rs1, Id_rs2, MeWb_rd, 1'b1, Wb_rslt2, Id_rrs1, Id_rrs2);

  wire [12:0] w_addr;
  wire w_vb;
  m_br_address m_addr (w_clk, IfId_pc[13:2], IfId_ir, Ex_taken, IdEx_pc[13:2], IdEx_tpc[12:0], Id_op5, Ex_op5, w_addr, w_vb);

  always @(posedge w_clk) #5 if(w_ce) begin
    IdEx_pc   <= (Ex_taken) ? 0 : IfId_pc;
    IdEx_ir   <= (Ex_taken) ? {25'd0, 7'b0010011} : IfId_ir;
    IdEx_tpc  <= IfId_pc + Id_imm;
    IdEx_imm  <= Id_imm;
    IdEx_rrs1 <= Id_rrs1;
    IdEx_rrs2 <= Id_rrs2;
    IdEx_rd   <= (Id_we==0 || Ex_taken) ? 0 : Id_rd; // Note
  end
  /*********************** Ex stage *********************************/
  wire [4:0] Ex_op5 = IdEx_ir[6:2];
  wire [4:0] Ex_rs1 = IdEx_ir[19:15]; // 5/23
  wire [4:0] Ex_rs2 = IdEx_ir[24:20]; // 5/23
  wire Ex_SLL = (IdEx_ir[14:12]==3'b001);
  wire Ex_SRL = (IdEx_ir[14:12]==3'b101);
  wire Ex_BEQ = ({IdEx_ir[12], Ex_op5}==6'b011000);
  wire Ex_BNE = ({IdEx_ir[12], Ex_op5}==6'b111000);
  wire [31:0] Ex_ain1 = (Ex_rs1==0) ? 0 : (Ex_rs1==Me_rd & Me_we) ? ExMe_rslt : (Ex_rs1==Wb_rd & Wb_we) ? Wb_rslt2 : IdEx_rrs1; // 5/23
  wire [31:0] Ex_ain2 = (Ex_rs2==0) ? 0 : (Ex_rs2==Me_rd & Me_we) ? ExMe_rslt : (Ex_rs2==Wb_rd & Wb_we) ? Wb_rslt2 : IdEx_rrs2; // 5/23
  wire [31:0] Ex_ain = (Ex_op5==5'b01100 || Ex_op5==5'b11000) ? Ex_ain2 : IdEx_imm; // 5/23
  wire [31:0] Ex_rslt = (Ex_SLL) ? Ex_ain1 << Ex_ain[4:0] : // 5/23
                        (Ex_SRL) ? Ex_ain1 >> Ex_ain[4:0] : Ex_ain1 + Ex_ain; // 5/23
  wire Ex_taken = (Ex_BEQ & Ex_ain1==Ex_ain) || (Ex_BNE & Ex_ain1!=Ex_ain); // 5/23
  always @(posedge w_clk) #5 if(w_ce) begin
    ExMe_pc   <= IdEx_pc;
    ExMe_ir   <= IdEx_ir;
    ExMe_rslt <= Ex_rslt;
    ExMe_rrs2 <= IdEx_rrs2;
    ExMe_rd   <= IdEx_rd;
  end
  /*********************** Me stage *********************************/
  wire [4:0] Me_op5 = ExMe_ir[6:2];   
  wire [4:0] Me_rd = ExMe_rd; // 5/23
  wire       Me_we = (Me_op5==5'b01100 || Me_op5==5'b00100 || Me_op5==5'b00000);
  wire [31:0] Me_ldd;
  m_amemory m_dmem (w_clk, ExMe_rslt[13:2], (Me_op5==5'b01000), ExMe_rrs2, Me_ldd);
  always @(posedge w_clk) #5 if(w_ce) begin
     MeWb_pc   <= ExMe_pc;
     MeWb_ir   <= ExMe_ir;
     MeWb_rslt <= ExMe_rslt;
     MeWb_ldd  <= Me_ldd;
     MeWb_rd   <= ExMe_rd;
  end
  /*********************** Wb stage *********************************/
  wire Wb_LW = (MeWb_ir[6:2]==5'b00000);
  wire [4:0] Wb_op5 = MeWb_ir[6:2]; // 5/23
  wire [4:0] Wb_rd = MeWb_rd; // 5/23
  wire       Wb_we = (Wb_op5==5'b01100 || Wb_op5==5'b00100 || Wb_op5==5'b00000); // 5/23
  wire [31:0] Wb_rslt2 = (Wb_LW) ? MeWb_ldd : MeWb_rslt;
  always @(posedge w_clk) #5
    if(w_ce && IfId_ir!=32'h000f0033) r_pc <= (Ex_taken) ? IdEx_tpc : r_pc+4;
   
  reg [31:0] r_led = 0;
  always @(posedge w_clk) if(w_ce & MeWb_rd==30) r_led <= Wb_rslt2;
  assign w_led = r_led;
endmodule

/**************************************************************************/
module m_amemory (w_clk, w_addr, w_we, w_din, w_dout); // asynchronous memory
  input  wire w_clk, w_we;
  input  wire [11:0] w_addr;
  input  wire [31:0] w_din;
  output wire [31:0] w_dout;
  reg [31:0] 	     cm_ram [0:4095]; // 4K word (4096 x 32bit) memory
  always @(posedge w_clk) if (w_we) cm_ram[w_addr] <= w_din;
  assign #20 w_dout = cm_ram[w_addr];
`include "program.txt"
endmodule

/**************************************************************************/
module m_memory (w_clk, w_addr, w_we, w_din, r_dout); // synchronous memory
  input  wire w_clk, w_we;
  input  wire [11:0] w_addr;
  input  wire [31:0] w_din;
  output reg  [31:0] r_dout;
  reg [31:0]         cm_ram [0:4095]; // 4K word (4096 x 32bit) memory
  always @(posedge w_clk) if (w_we) cm_ram[w_addr] <= w_din;
  always @(posedge w_clk) r_dout <= cm_ram[w_addr];
`include "program.txt"
endmodule

/**************************************************************************/
module m_immgen (w_i, r_imm); // module immediate generator
  input  wire [31:0] w_i;    // instruction
  output reg  [31:0] r_imm;  // r_immediate

  always @(*) case (w_i[6:2])
    5'b11000: r_imm <= {{20{w_i[31]}}, w_i[7], w_i[30:25], w_i[11:8], 1'b0};   // B-type
    5'b01000: r_imm <= {{21{w_i[31]}}, w_i[30:25], w_i[11:7]};                 // S-type
    5'b11011: r_imm <= {{12{w_i[31]}}, w_i[19:12], w_i[20], w_i[30:21], 1'b0}; // J-type
    5'b01101: r_imm <= {w_i[31:12], 12'b0};                                    // U-type
    5'b00101: r_imm <= {w_i[31:12], 12'b0};                                    // U-type
    default : r_imm <= {{21{w_i[31]}}, w_i[30:20]};                   // I-type & R-type
  endcase
endmodule

/**************************************************************************/
module m_rf_bypass (w_clk, w_rr1, w_rr2, w_wr, w_we, w_wdata, w_rdata1, w_rdata2); // 5/23
   input  wire        w_clk;
   input  wire [4:0]  w_rr1, w_rr2, w_wr;
   input  wire [31:0] w_wdata;
   input  wire        w_we;
   output wire [31:0] w_rdata1, w_rdata2;
    
   reg [31:0] r[0:31];
   assign #8 w_rdata1 = (w_rr1==0) ? 0 : (w_rr1==w_wr & w_we) ? w_wdata : r[w_rr1]; // 5/23
   assign #8 w_rdata2 = (w_rr2==0) ? 0 : (w_rr2==w_wr & w_we) ? w_wdata : r[w_rr2]; // 5/23
   always @(posedge w_clk) if(w_we) r[w_wr] <= w_wdata;
endmodule
/**************************************************************************/
module m_br_address (w_clk, IfId_pc, IfId_ir, Ex_taken, IdEx_pc, IdEx_tpc, Id_op5, Ex_op5, w_addr, w_vb);
  input  wire w_clk;
  input  wire [11:0] IfId_pc;
  input  wire [31:0] IfId_ir;
  input  wire Ex_taken;
  input  wire [11:0] IdEx_pc;
  input  wire [12:0] IdEx_tpc;
  input  wire [4:0]  Id_op5;
  input  wire [4:0]  Ex_op5;
  output wire [12:0] w_addr;
  output wire w_vb;

  reg [13:0] addr_ram [0:4095]; // 13-bit address RAM with MSB as valid bit
  integer i;

  initial begin
    for (i = 0; i < 4096; i = i + 1) begin
      addr_ram[i] = 14'd0;
    end
  end

  always @(posedge w_clk) begin
    if (Ex_op5 == 5'b11100) begin // BNE instruction
      if (addr_ram[IdEx_pc[13:2]][12:0] == IdEx_tpc) begin
        addr_ram[IdEx_pc[13:2]] <= {1'b0, addr_ram[IdEx_pc[13:2]][12:0]};
      end else begin
        addr_ram[IdEx_pc[13:2]] <= {1'b1, IdEx_tpc};
      end
    end
  end

  assign w_vb = (Id_op5 == 5'b11100 && IfId_pc == IdEx_pc) ? 1'b1 : 1'b0;
  assign w_addr = (Id_op5 == 5'b11100) ? addr_ram[IfId_pc[13:2]][12:0] : 13'b0;
endmodule
/**************************************************************************/
