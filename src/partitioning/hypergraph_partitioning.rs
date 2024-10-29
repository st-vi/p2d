use std::ptr;
use crate::partitioning::patoh_api::{PaToH_Alloc, PaToH_Free, PaToH_Initialize_Parameters, PaToH_Parameters, PaToH_Part, PATOH_CONPART, PATOH_SUGPARAM_QUALITY};
use libc::{c_int, free, malloc};

pub fn partition(number_vertices: u32, number_nets: u32, nets: &Vec<u32>, x_pins: &Vec<u32>) -> (u32, Vec<u32>, Vec<u32>) {
    unsafe {
        let mut args: PaToH_Parameters = PaToH_Parameters {
            cuttype: 0,
            _k: 2,
            outputdetail: 0,
            seed: 1,
            doinitperm: 0,
            bisec_fixednetsizetrsh: 0,
            bisec_netsizetrsh: 0.0,
            bisec_partmultnetsizetrsh: 0,
            bigVcycle: 0,
            smallVcycle: 0,
            usesamematchinginVcycles: 0,
            usebucket: 0,
            maxcellinheap: 0,
            heapchk_mul: 0,
            heapchk_div: 0,
            MemMul_CellNet: 0,
            MemMul_Pins: 0,
            MemMul_General: 0,
            crs_VisitOrder: 0,
            crs_alg: 0,
            crs_coarsento: 0,
            crs_coarsentokmult: 0,
            crs_coarsenper: 0,
            crs_maxallowedcellwmult: 0.0,
            crs_idenafter: 0,
            crs_iden_netsizetrh: 0,
            crs_useafter: 0,
            crs_useafteralg: 0,
            nofinstances: 0,
            initp_alg: 0,
            initp_runno: 0,
            initp_ghg_trybalance: 0,
            initp_refalg: 0,
            ref_alg: 0,
            ref_useafter: 0,
            ref_useafteralg: 0,
            ref_passcnt: 0,
            ref_maxnegmove: 0,
            ref_maxnegmovemult: 0.0,
            ref_dynamiclockcnt: 0,
            ref_slow_uncoarsening: 0.0,
            balance: 0,
            init_imbal: 0.0,
            final_imbal: 0.0,
            fast_initbal_mult: 0.0,
            init_sol_discard_mult: 0.0,
            final_sol_discard_mult: 0.0,
            allargs: [0; 8192],
            inputfilename: [0; 512],
            noofrun: 0,
            writepartinfo: 0,
        };

        let c: c_int = number_vertices as c_int;
        let n: c_int = number_nets as c_int;
        let nconst: c_int = 1;
        let cwghts: *mut c_int = malloc((c as usize * std::mem::size_of::<c_int>()) as libc::size_t) as *mut c_int;
        let nwghts: *mut c_int = malloc((n as usize * std::mem::size_of::<c_int>()) as libc::size_t) as *mut c_int;
        let xpins: *mut c_int = malloc((x_pins.len() * std::mem::size_of::<c_int>()) as libc::size_t) as *mut c_int;
        let pins: *mut c_int = malloc((nets.len() * std::mem::size_of::<c_int>()) as libc::size_t) as *mut c_int;
        let partvec: *mut c_int = malloc((c as usize * std::mem::size_of::<c_int>()) as libc::size_t) as *mut c_int;
        let mut cut: c_int = 0;
        let partweights: *mut c_int = malloc(args._k as usize * std::mem::size_of::<c_int>() as libc::size_t) as *mut c_int;

        for i in 0..c {
            *cwghts.wrapping_add(i as usize) = 1;
        }
        for i in 0..n {
            *nwghts.wrapping_add(i as usize) = 1;
        }
        for i in 0..x_pins.len() {
            *xpins.wrapping_add(i) = *x_pins.get(i).unwrap() as c_int;
        }
        for i in 0..nets.len() {
            *pins.wrapping_add(i) = *nets.get(i).unwrap() as c_int;
        }

        PaToH_Initialize_Parameters(
            &mut args,
            PATOH_CONPART as c_int,
            PATOH_SUGPARAM_QUALITY as c_int
        );

        args.seed = 1;

        PaToH_Alloc(
            &mut args,
            c,
            n,
            nconst,
            cwghts,
            nwghts,
            xpins,
            pins
        );


        PaToH_Part(
            &mut args,
            c,
            n,
            nconst,
            0,
            cwghts,
            nwghts,
            xpins,
            pins,
            ptr::null_mut(),
            partvec,
            partweights,
            &mut cut
        );



        //let res = PaToH_Check_Hypergraph(c, n, nconst, cwghts, nwghts, xpins, pins);

        let mut edges_to_remove = Vec::new();
        for i in 0..n {
            let mut partition_set = std::collections::HashSet::new();
            for j in *xpins.wrapping_add(i as usize)..*xpins.wrapping_add((i + 1) as usize) {
                let pin = *pins.wrapping_add(j as usize);
                let tmp = *partvec.wrapping_add(pin as usize);
                partition_set.insert(tmp);
            }
            if partition_set.len() > 1 {
                edges_to_remove.push(i as u32);
            }
        }

        let mut partition = Vec::new();
        for i in 0..c {
            partition.push(*partvec.wrapping_add(i as usize) as u32);
        }

        free(cwghts as *mut libc::c_void);
        free(nwghts as *mut libc::c_void);
        free(xpins as *mut libc::c_void);
        free(pins as *mut libc::c_void);
        free(partvec as *mut libc::c_void);
        free(partweights as *mut libc::c_void);
        PaToH_Free();

        (cut as u32, partition, edges_to_remove)
    }
}